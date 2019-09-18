use std::convert::{TryFrom, TryInto};

use cranelift::codegen::{
    self,
    ir::{
        condcodes,
        entities::StackSlot,
        function::Function,
        stackslot::{StackSlotData, StackSlotKind},
        ExternalName, InstBuilder, MemFlags,
    },
    isa,
    settings::{self, Configurable},
};
use cranelift::prelude::{
    types, Ebb, FunctionBuilder, FunctionBuilderContext, Signature, Type as IrType,
    Value as IrValue,
};
use cranelift_faerie::{FaerieBackend, FaerieBuilder, FaerieTrapCollection};
use cranelift_module::{self, DataContext, DataId, FuncId, Linkage, Module as CraneliftModule};

use crate::backend::TARGET;
use crate::data::{
    prelude::*, ArrayType, FunctionType, Initializer, Scope, StorageClass, StructType,
};
use crate::utils::warn;

type Module = CraneliftModule<FaerieBackend>;
type IrResult = SemanticResult<Value>;

enum Id {
    Function(FuncId),
    Global(DataId),
    Local(StackSlot),
}

enum FuncCall {
    Named(String),
    Indirect(Value),
}

struct Compiler {
    module: Module,
    ebb_has_return: bool,
    scope: Scope<String, Id>,
    debug: bool,
    str_index: usize,
    loops: Vec<(Ebb, Ebb)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Value {
    ir_val: IrValue,
    ir_type: IrType,
    ctype: Type,
}

/// Compile a program from a high level IR to a Cranelift Module
pub(crate) fn compile(program: Vec<Locatable<Declaration>>, debug: bool) -> SemanticResult<Module> {
    let name = program
        .first()
        .map_or_else(|| "<empty>".to_string(), |decl| decl.location.file.clone());
    let mut compiler = Compiler::new(name, debug);
    for decl in program {
        match (decl.data.symbol.ctype.clone(), decl.data.init) {
            (Type::Function(func_type), None) => {
                let location = decl.location;
                compiler.declare_func(
                    decl.data.symbol.id,
                    &func_type.signature(&location)?,
                    decl.data.symbol.storage_class,
                    &location,
                    // TODO: this doesn't allow declaring a function and then defining it
                    // TODO: the reason this is here is because if you declare a function without defining it
                    // e.g. `int puts(char *)`, Cranelift will throw an error
                    // TODO: to work around this, you can use `static` when declaring a function instead,
                    // or just define a function up front
                    true,
                )?;
            }
            (Type::Void, _) => unreachable!("parser let an incomplete type through"),
            (Type::Function(func_type), Some(Initializer::FunctionBody(stmts))) => compiler
                .compile_func(
                    decl.data.symbol.id,
                    func_type,
                    decl.data.symbol.storage_class,
                    stmts,
                    decl.location,
                )?,
            (_, Some(Initializer::FunctionBody(_))) => {
                unreachable!("only functions should have a function body")
            }
            (_, init) => compiler.store_static(decl.data.symbol, init, decl.location)?,
        }
    }
    Ok(compiler.module)
}

impl Compiler {
    fn new(name: String, debug: bool) -> Compiler {
        let mut flags_builder = settings::builder();
        // allow creating shared libraries
        flags_builder
            .enable("is_pic")
            .expect("is_pic should be a valid option");
        // use debug assertions
        flags_builder
            .enable("enable_verifier")
            .expect("enable_verifier should be a valid option");
        // compile quickly, but without optimizations
        flags_builder
            .set("opt_level", "fastest")
            .expect("opt_level: fastest should be a valid option");

        let isa = isa::lookup(TARGET.clone())
            .unwrap_or_else(|_| panic!("platform not supported: {}", *TARGET))
            .finish(settings::Flags::new(flags_builder));

        let builder = FaerieBuilder::new(
            isa,
            name,
            FaerieTrapCollection::Disabled,
            cranelift_module::default_libcall_names(),
        )
        .expect("unknown error creating module");

        Compiler {
            module: Module::new(builder),
            ebb_has_return: false,
            scope: Scope::new(),
            loops: Vec::new(),
            str_index: 0,
            debug,
        }
    }
    fn declare_func(
        &mut self,
        id: String,
        signature: &Signature,
        sc: StorageClass,
        location: &Location,
        cextern: bool,
    ) -> SemanticResult<FuncId> {
        let mut linkage = sc.try_into().map_err(|err| Locatable {
            data: err,
            location: location.clone(),
        })?;
        if linkage == Linkage::Export && cextern {
            linkage = Linkage::Import;
        }
        let func_id = self
            .module
            .declare_function(&id, linkage, &signature)
            .expect("should not have an error declaring a function");
        self.scope.insert(id, Id::Function(func_id));
        Ok(func_id)
    }
    /// declare an object on the stack
    fn declare_data(
        &mut self,
        decl: Declaration,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        if let Type::Function(ftype) = decl.symbol.ctype {
            self.declare_func(
                decl.symbol.id,
                &ftype.signature(&location)?,
                decl.symbol.storage_class,
                &location,
                true,
            )?;
            return Ok(());
        }
        let u64_size = match decl.symbol.ctype.sizeof() {
            Ok(size) => size,
            Err(err) => {
                return Err(Locatable {
                    data: err.into(),
                    location,
                })
            }
        };
        let kind = StackSlotKind::ExplicitSlot;
        let size = match u32::try_from(u64_size) {
            Ok(size) => size,
            Err(_) => return Err(Locatable {
                data: "cannot store items on the stack that are more than 4 GB, it will overflow the stack".into(),
                location,
            })
        };
        let data = StackSlotData {
            kind,
            size,
            offset: None,
        };
        let stack_slot = builder.create_stack_slot(data);
        self.scope.insert(decl.symbol.id, Id::Local(stack_slot));
        if let Some(init) = decl.init {
            self.store_stack(init, stack_slot, decl.symbol.ctype, location, builder)?;
        }
        Ok(())
    }
    fn store_stack(
        &mut self,
        init: Initializer,
        stack_slot: StackSlot,
        ctype: Type,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        match init {
            Initializer::Scalar(expr) => {
                let val = self.compile_expr(*expr, builder)?;
                // TODO: replace with `builder.ins().stack_store(val.ir_val, stack_slot, 0);`
                // when Cranelift implements stack_store for i8 and i16
                let addr = builder.ins().stack_addr(Type::ptr_type(), stack_slot, 0);
                builder.ins().store(MemFlags::new(), val.ir_val, addr, 0);
            }
            Initializer::InitializerList(_) => unimplemented!("aggregate dynamic initialization"),
            Initializer::FunctionBody(_) => unreachable!("functions can't be stored on the stack"),
        }
        Ok(())
    }
    // TODO: this is grossly inefficient, ask Cranelift devs if
    // there's an easier way to make parameters modifiable.
    fn store_stack_params(
        &mut self,
        params: Vec<Symbol>,
        func_start: Ebb,
        location: &Location,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        // Cranelift requires that all EBB params are declared up front
        let ir_vals: Vec<_> = params
            .iter()
            .map(|param| {
                let ir_type = match param.ctype.as_ir_type() {
                    Err(data) => err!(data, location.clone()),
                    Ok(ir_type) => ir_type,
                };
                Ok(builder.append_ebb_param(func_start, ir_type))
            })
            .collect::<Result<_, Locatable<String>>>()?;
        for (param, ir_val) in params.into_iter().zip(ir_vals) {
            let ir_type = param
                .ctype
                .as_ir_type()
                .expect("errors should already have been caught when adding ebb params");
            let u64_size = match param.ctype.sizeof() {
                Err(data) => err!(data.into(), location.clone()),
                Ok(size) => size,
            };
            let u32_size = match u32::try_from(u64_size) {
                Err(_) => err!(
                    format!(
                        "size {} is too large for stack (can only handle 32-bit values)",
                        u64_size
                    ),
                    location.clone()
                ),
                Ok(size) => size,
            };
            let stack_data = StackSlotData {
                kind: StackSlotKind::ExplicitSlot,
                size: u32_size,
                offset: None,
            };
            let slot = builder.create_stack_slot(stack_data);
            // TODO: need to take the address before storing until Cranelift implements
            // stores for i8 and i16
            // then this can be replaced with `builder.ins().stack_store(ir_val, slot, 0);`
            // See https://github.com/CraneStation/cranelift/issues/433
            let addr = builder.ins().stack_addr(Type::ptr_type(), slot, 0);
            builder.ins().store(MemFlags::new(), ir_val, addr, 0);
            self.scope.insert(param.id, Id::Local(slot));
        }
        Ok(())
    }
    fn compile_func(
        &mut self,
        id: String,
        func_type: FunctionType,
        sc: StorageClass,
        stmts: Vec<Stmt>,
        location: Location,
    ) -> SemanticResult<()> {
        let signature = func_type.signature(&location)?;
        let func_id = self.declare_func(id.clone(), &signature, sc, &location, false)?;
        // external name is meant to be a lookup in a symbol table,
        // but we just give it garbage values
        let mut func = Function::with_name_signature(ExternalName::user(0, 0), signature);

        // this context is just boiler plate
        let mut ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut ctx);

        let func_start = builder.create_ebb();
        builder.switch_to_block(func_start);
        self.ebb_has_return = false;

        let should_ret = func_type.should_return();
        if func_type.has_params() {
            self.store_stack_params(func_type.params, func_start, &location, &mut builder)?;
        }
        self.compile_all(stmts, &mut builder)?;
        if !self.ebb_has_return {
            if id == "main" {
                let ir_int = func_type
                    .return_type
                    .as_ir_type()
                    .expect("main should return an int");
                let zero = [builder.ins().iconst(ir_int, 0)];
                builder.ins().return_(&zero);
            } else if should_ret {
                err!(
                    format!(
                        "expected a return statement before end of function '{}' returning {}",
                        id, func_type.return_type
                    ),
                    location
                );
            } else {
                // void function, return nothing
                builder.ins().return_(&[]);
            }
        }
        if self.debug {
            let mut clif = String::new();
            codegen::write_function(&mut clif, &func, &None.into()).unwrap();
            println!("{}", clif);
        }

        let flags = settings::Flags::new(settings::builder());
        codegen::verify_function(&func, &flags).expect("should not have a compile error");

        let mut ctx = codegen::Context::for_function(func);
        self.module
            .define_function(func_id, &mut ctx)
            .expect("should not have an error defining a function");
        Ok(())
    }
    fn compile_all(
        &mut self,
        stmts: Vec<Stmt>,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        for stmt in stmts {
            self.compile_stmt(stmt, builder)?;
        }
        Ok(())
    }
    fn compile_stmt(&mut self, stmt: Stmt, builder: &mut FunctionBuilder) -> SemanticResult<()> {
        if self.ebb_has_return {
            return Err(Locatable {
                data: "unreachable statement".into(),
                location: stmt.location,
            });
        }
        match stmt.data {
            StmtType::Compound(stmts) => self.compile_all(stmts, builder),
            // INVARIANT: symbol has not yet been declared in this scope
            StmtType::Decl(decls) => {
                for decl in decls {
                    self.declare_data(decl.data, decl.location, builder)?;
                }
                Ok(())
            }
            StmtType::Expr(expr) => {
                self.compile_expr(expr, builder)?;
                Ok(())
            }
            StmtType::Return(expr) => {
                let mut ret = vec![];
                if let Some(e) = expr {
                    let val = self.compile_expr(e, builder)?;
                    ret.push(val.ir_val);
                }
                self.ebb_has_return = true;
                builder.ins().return_(&ret);
                Ok(())
            }
            StmtType::If(condition, body, otherwise) => {
                self.if_stmt(condition, *body, otherwise, builder)
            }
            StmtType::While(condition, maybe_body) => {
                self.while_stmt(condition, maybe_body, builder)
            }
            StmtType::Break | StmtType::Continue => {
                self.loop_exit(stmt.data == StmtType::Break, stmt.location, builder)
            }
            StmtType::For(decls, condition, post_loop, body) => unimplemented!("codegen for-loop"),
            StmtType::Do(body, expr) => unimplemented!("codegen do-while-loop"),
            StmtType::Switch(expr, body) => unimplemented!("codegen switch"),
            StmtType::Label(label) | StmtType::Goto(label) => unimplemented!("codegen goto"),
            StmtType::Case(expr) => unimplemented!("codegen case"),
            StmtType::Default => unimplemented!("codegen case"),
        }
    }
    // clippy doesn't like big match statements, but this is kind of essential complexity,
    // it can't be any smaller without supporting fewer features
    #[allow(clippy::cognitive_complexity)]
    fn compile_expr(&mut self, expr: Expr, builder: &mut FunctionBuilder) -> IrResult {
        let expr = expr.const_fold()?;
        let location = expr.location;
        let ir_type = if expr.lval {
            Type::ptr_type()
        } else if expr.ctype == Type::Void {
            types::INVALID
        } else {
            match expr.ctype.as_ir_type() {
                Ok(ir_type) => ir_type,
                Err(err) => {
                    return Err(Locatable {
                        data: err,
                        location,
                    });
                }
            }
        };
        match expr.expr {
            ExprType::Literal(token) => {
                self.compile_literal(ir_type, expr.ctype, token, location, builder)
            }
            ExprType::Id(var) => self.load_addr(var, location, builder),

            // unary operators
            ExprType::Deref(pointer) => {
                let val = self.compile_expr(*pointer, builder)?;
                let flags = MemFlags::new();
                Ok(Value {
                    ir_type,
                    ctype: expr.ctype,
                    ir_val: builder.ins().load(ir_type, flags, val.ir_val, 0),
                })
            }
            // NOTE: this may be an implicit cast (float f = 1.2) not an explicit cast (1 + (int)1.2)
            // NOTE: it may also be a widening conversion (1 + 1.2)
            ExprType::Cast(orig) => self.cast(*orig, expr.ctype, location, builder),
            ExprType::Negate(expr) => self.negate(*expr, builder),
            ExprType::BitwiseNot(expr) => self.unary_op(
                *expr,
                builder,
                |ir_val, ir_type, _, builder| match ir_type {
                    ty if ty.is_int() => builder.ins().bnot(ir_val),
                    _ => unreachable!("parser should catch illegal types"),
                },
            ),
            ExprType::LogicalNot(expr) => self.logical_not(*expr, builder),

            // binary operators
            ExprType::Add(left, right) => {
                self.binary_assign_op(*left, *right, expr.ctype, Token::Plus, location, builder)
            }
            ExprType::Sub(left, right) => {
                self.binary_assign_op(*left, *right, expr.ctype, Token::Minus, location, builder)
            }
            ExprType::Mul(left, right) => {
                self.binary_assign_op(*left, *right, expr.ctype, Token::Star, location, builder)
            }
            ExprType::Div(left, right) => {
                self.binary_assign_op(*left, *right, expr.ctype, Token::Divide, location, builder)
            }
            ExprType::Mod(left, right) => {
                self.binary_assign_op(*left, *right, expr.ctype, Token::Mod, location, builder)
            }
            ExprType::BitwiseAnd(left, right) => self.binary_assign_op(
                *left,
                *right,
                expr.ctype,
                Token::Ampersand,
                location,
                builder,
            ),
            ExprType::BitwiseOr(left, right) => self.binary_assign_op(
                *left,
                *right,
                expr.ctype,
                Token::BitwiseOr,
                location,
                builder,
            ),
            // left shift
            ExprType::Shift(left, right, true) => self.binary_assign_op(
                *left,
                *right,
                expr.ctype,
                Token::ShiftRight,
                location,
                builder,
            ),
            // right shift
            ExprType::Shift(left, right, false) => self.binary_assign_op(
                *left,
                *right,
                expr.ctype,
                Token::ShiftRight,
                location,
                builder,
            ),
            ExprType::Xor(left, right) => {
                self.binary_assign_op(*left, *right, expr.ctype, Token::Xor, location, builder)
            }
            ExprType::Compare(left, right, token) => self.compare(*left, *right, &token, builder),

            // misfits
            ExprType::Assign(lval, rval, token) => {
                self.assignment(*lval, *rval, token, location, builder)
            }
            ExprType::FuncCall(func, args) => match func.expr {
                ExprType::Id(var) => self.call(
                    FuncCall::Named(var.id),
                    func.ctype,
                    args,
                    &location,
                    builder,
                ),
                _ => {
                    let ctype = func.ctype.clone();
                    let val = self.compile_expr(*func, builder)?;
                    self.call(FuncCall::Indirect(val), ctype, args, &location, builder)
                }
            },
            ExprType::Comma(left, right) => {
                self.compile_expr(*left, builder)?;
                self.compile_expr(*right, builder)
            }
            ExprType::Member(cstruct, id) => {
                let ctype = cstruct.ctype.clone();
                let pointer = self.compile_expr(*cstruct, builder)?;
                let id = if let Token::Id(id) = id {
                    id
                } else {
                    unreachable!("parser should only pass ids to ExprType::Member");
                };
                let offset = match &ctype {
                    Type::Struct(StructType::Anonymous(members)) => {
                        ctype.struct_offset(members, &id)
                    }
                    Type::Struct(StructType::Named(_, _, _, offsets)) => *offsets.get(&id).unwrap(),
                    Type::Union(_) => 0,
                    _ => unreachable!("only structs and unions can have members"),
                };
                let ir_offset = builder.ins().iconst(Type::ptr_type(), offset as i64);
                Ok(Value {
                    ir_val: builder.ins().iadd(pointer.ir_val, ir_offset),
                    ir_type,
                    ctype,
                })
            }
            x => {
                unimplemented!("{:?}", x);
            }
        }
    }
    fn compile_literal(
        &mut self,
        ir_type: IrType,
        ctype: Type,
        token: Token,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        let ir_val = match (token, ir_type) {
            (Token::Int(i), types::B1) => builder.ins().bconst(ir_type, i != 0),
            (Token::Int(i), _) => builder.ins().iconst(ir_type, i),
            (Token::UnsignedInt(u), types::B1) => builder.ins().bconst(ir_type, u != 0),
            (Token::UnsignedInt(u), _) => builder.ins().iconst(ir_type, u as i64),
            (Token::Float(f), types::F32) => builder.ins().f32const(f as f32),
            (Token::Float(f), types::F64) => builder.ins().f64const(f),
            (Token::Char(c), _) => builder.ins().iconst(ir_type, i64::from(c)),
            (Token::Str(string), _) => self.compile_string(string, builder, location)?,
            _ => unimplemented!("aggregate literals"),
        };
        Ok(Value {
            ir_val,
            ir_type,
            ctype,
        })
    }
    fn compile_string(
        &mut self,
        string: String,
        builder: &mut FunctionBuilder,
        location: Location,
    ) -> SemanticResult<IrValue> {
        let name = format!("str.{}", self.str_index);
        self.str_index += 1;
        let str_id = match self.module.declare_data(&name, Linkage::Local, false, None) {
            Ok(id) => id,
            Err(err) => err!(format!("error declaring static string: {}", err), location),
        };
        let mut ctx = DataContext::new();
        ctx.define(string.into_bytes().into_boxed_slice());
        self.module
            .define_data(str_id, &ctx)
            .map_err(|err| Locatable {
                data: format!("error defining static string: {}", err),
                location,
            })?;
        let addr = self.module.declare_data_in_func(str_id, builder.func);
        Ok(builder.ins().global_value(Type::ptr_type(), addr))
    }
    fn unary_op<F>(&mut self, expr: Expr, builder: &mut FunctionBuilder, func: F) -> IrResult
    where
        F: FnOnce(IrValue, IrType, &Type, &mut FunctionBuilder) -> IrValue,
    {
        let ctype = expr.ctype.clone();
        let val = self.compile_expr(expr, builder)?;
        let ir_val = func(val.ir_val, val.ir_type, &ctype, builder);
        Ok(Value {
            ir_val,
            ctype,
            ir_type: val.ir_type,
        })
    }
    #[inline]
    fn binary_assign_op(
        &mut self,
        left: Expr,
        right: Expr,
        ctype: Type,
        token: Token,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        let (left, right) = (
            self.compile_expr(left, builder)?,
            self.compile_expr(right, builder)?,
        );
        Self::binary_assign_ir(left, right, ctype, token, location, builder)
    }
    fn binary_assign_ir(
        left: Value,
        right: Value,
        ctype: Type,
        token: Token,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        use codegen::ir::InstBuilder as b;
        assert_eq!(left.ir_type, right.ir_type);
        let ir_type = ctype
            .as_ir_type()
            .map_err(|data| Locatable { data, location })?;
        let signed = ctype.is_signed();
        let func = match (token, ir_type, signed) {
            (Token::Plus, ty, _) if ty.is_int() => b::iadd,
            (Token::Plus, ty, _) if ty.is_float() => b::fadd,
            (Token::Minus, ty, _) if ty.is_int() => b::isub,
            (Token::Minus, ty, _) if ty.is_float() => b::fsub,
            (Token::Star, ty, _) if ty.is_int() => b::imul,
            (Token::Star, ty, _) if ty.is_float() => b::fmul,
            (Token::Divide, ty, true) if ty.is_int() => b::sdiv,
            (Token::Divide, ty, false) if ty.is_int() => b::udiv,
            (Token::Divide, ty, _) if ty.is_float() => b::fdiv,
            (Token::Mod, ty, true) if ty.is_int() => b::srem,
            (Token::Mod, ty, false) if ty.is_int() => b::urem,
            (Token::Ampersand, ty, _) if ty.is_int() => b::band,
            (Token::BitwiseOr, ty, _) if ty.is_int() => b::bor,
            (Token::ShiftLeft, ty, _) if ty.is_int() => b::ishl,
            // arithmetic shift: keeps the sign of `left`
            (Token::ShiftRight, ty, true) if ty.is_int() => b::sshr,
            // logical shift: shifts in zeros
            (Token::ShiftRight, ty, false) if ty.is_int() => b::ushr,
            (Token::Xor, ty, _) if ty.is_int() => b::bxor,
            (token, _, _) => unreachable!(
                "only valid assign binary ops should be passed to binary_assign_op (got {})",
                token
            ),
        };
        let ir_val = func(builder.ins(), left.ir_val, right.ir_val);
        Ok(Value {
            ir_val,
            ir_type,
            ctype,
        })
    }
    fn cast(
        &mut self,
        expr: Expr,
        ctype: Type,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        // calculate this here before it's moved to `compile_expr`
        let orig_signed = expr.ctype.is_signed();
        let original = self.compile_expr(expr, builder)?;
        let cast_type = ctype.as_ir_type().map_err(|err| Locatable {
            data: err,
            location,
        })?;
        let cast = Self::cast_ir(
            original.ir_type,
            cast_type,
            original.ir_val,
            orig_signed,
            ctype.is_signed(),
            builder,
        );
        Ok(Value {
            ir_val: cast,
            ir_type: cast_type,
            ctype,
        })
    }
    fn cast_ir(
        from: IrType,
        to: IrType,
        val: IrValue,
        from_signed: bool,
        to_signed: bool,
        builder: &mut FunctionBuilder,
    ) -> IrValue {
        // NOTE: we compare the IR types, not the C types, because multiple C types
        // NOTE: may have the same representation (e.g. both `int` and `long` are i64)
        if from == to {
            // no-op
            return val;
        }
        match (from, to) {
            // narrowing and widening float conversions
            (types::F32, types::F64) => builder.ins().fpromote(to, val),
            (types::F64, types::F32) => builder.ins().fdemote(to, val),
            // narrowing and widening integer conversions
            (b, i) if b.is_bool() && i.is_int() => builder.ins().bint(to, val),
            (i, b) if i.is_int() && b.is_bool() => {
                builder.ins().icmp_imm(condcodes::IntCC::NotEqual, val, 0)
            }
            (big_int, small_int)
                if big_int.is_int()
                    && small_int.is_int()
                    && big_int.lane_bits() > small_int.lane_bits() =>
            {
                builder.ins().ireduce(small_int, val)
            }
            (small_int, big_int)
                if big_int.is_int()
                    && small_int.is_int()
                    && big_int.lane_bits() > small_int.lane_bits() =>
            {
                if to_signed {
                    builder.ins().sextend(big_int, val)
                } else {
                    builder.ins().uextend(big_int, val)
                }
            }
            // int/float conversions
            (i, f) if i.is_int() && f.is_float() => {
                if from_signed {
                    builder.ins().fcvt_from_sint(to, val)
                } else {
                    builder.ins().fcvt_from_uint(to, val)
                }
            }
            (f, i) if f.is_float() && i.is_int() => {
                if to_signed {
                    builder.ins().fcvt_to_sint(to, val)
                } else {
                    builder.ins().fcvt_to_uint(to, val)
                }
            }
            // bool/float conversions
            // cranelift doesn't seem to have a builtin way to do this
            // instead, this converts from bool to signed int and then int to float
            (b, f) if b.is_bool() && f.is_float() => {
                let int_val = Self::cast_ir(b, types::I32, val, false, true, builder);
                Self::cast_ir(types::I8, f, int_val, true, true, builder)
            }
            (f, b) if b.is_bool() && f.is_float() => {
                let int_val = Self::cast_ir(f, types::I32, val, true, true, builder);
                Self::cast_ir(types::I8, b, int_val, true, false, builder)
            }
            _ => unreachable!("cast from {} to {}", from, to),
        }
    }
    fn logical_not(&mut self, expr: Expr, builder: &mut FunctionBuilder) -> IrResult {
        self.unary_op(expr, builder, |ir_val, ir_type, ctype, builder| {
            let ir_bool = match ir_type {
                types::F32 => {
                    let zero = builder.ins().f32const(0.0);
                    builder.ins().fcmp(condcodes::FloatCC::Equal, ir_val, zero)
                }
                types::F64 => {
                    let zero = builder.ins().f64const(0.0);
                    builder.ins().fcmp(condcodes::FloatCC::Equal, ir_val, zero)
                }
                ty if ty.is_int() => builder.ins().icmp_imm(condcodes::IntCC::Equal, ir_val, 0),
                ty if ty.is_bool() => {
                    // TODO: change this if Cranelift ever implements boolean negation on x86
                    // see https://github.com/CraneStation/cranelift/issues/922
                    let int = Self::cast_ir(ir_type, types::I32, ir_val, false, true, builder);
                    builder.ins().icmp_imm(condcodes::IntCC::Equal, int, 0)
                }
                _ => unreachable!("all scalars should be float, int, or bool"),
            };
            Self::cast_ir(
                types::B1,
                ir_type,
                ir_bool,
                false,
                ctype.is_signed(),
                builder,
            )
        })
    }
    fn negate(&mut self, expr: Expr, builder: &mut FunctionBuilder) -> IrResult {
        self.unary_op(expr, builder, |ir_val, ir_type, _, builder| match ir_type {
            i if i.is_int() => builder.ins().irsub_imm(ir_val, 0),
            f if f.is_float() => builder.ins().fneg(ir_val),
            _ => unreachable!("parser should catch illegal types"),
        })
    }
    fn load_addr(
        &self,
        var: Symbol,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        let ptr_type = Type::ptr_type();
        let ir_val = match self.scope.get(&var.id).unwrap() {
            Id::Function(func_id) => {
                let func_ref = self.module.declare_func_in_func(*func_id, builder.func);
                builder.ins().func_addr(ptr_type, func_ref)
            }
            Id::Global(static_id) => {
                let global = self.module.declare_data_in_func(*static_id, builder.func);
                builder.ins().global_value(ptr_type, global)
            }
            Id::Local(stack_slot) => builder.ins().stack_addr(ptr_type, *stack_slot, 0),
        };
        Ok(Value {
            ir_type: ptr_type,
            ir_val,
            ctype: var.ctype,
        })
    }
    fn compare(
        &mut self,
        left: Expr,
        right: Expr,
        token: &Token,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        let (left, right) = (
            self.compile_expr(left, builder)?,
            self.compile_expr(right, builder)?,
        );
        assert_eq!(left.ir_type, right.ir_type);

        let ir_val = if left.ir_type.is_int() {
            let code = token
                .to_int_compare(left.ctype.is_signed())
                .expect("Expr::Compare should only have comparison tokens");
            builder.ins().icmp(code, left.ir_val, right.ir_val)
        } else {
            assert!(left.ir_type.is_float());
            let code = token
                .to_float_compare()
                .expect("Expr::Compare should only have comparison tokens");
            builder.ins().fcmp(code, left.ir_val, right.ir_val)
        };
        Ok(Value {
            ir_val,
            ir_type: types::B1,
            ctype: left.ctype,
        })
    }
    fn assignment(
        &mut self,
        lval: Expr,
        rval: Expr,
        token: Token,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        let ctype = lval.ctype.clone();
        let is_id = match lval.expr {
            ExprType::Id(_) => true,
            _ => false,
        };
        let (mut target, mut value) = (
            self.compile_expr(lval, builder)?,
            self.compile_expr(rval, builder)?,
        );
        let ir_target = if token != Token::Equal {
            let ir_target = target.ir_val;
            // need to deref explicitly to get an rval, the frontend didn't do it for us
            if is_id {
                let ir_type = match target.ctype.as_ir_type() {
                    Ok(ty) => ty,
                    Err(data) => err!(data, location),
                };
                target = Value {
                    ir_val: builder
                        .ins()
                        .load(ir_type, MemFlags::new(), target.ir_val, 0),
                    ir_type,
                    ctype: target.ctype,
                };
            }
            if target.ir_type != value.ir_type {
                unimplemented!("binary promotion for complex assignment");
            }
            value = Self::binary_assign_ir(
                target,
                value,
                ctype,
                token
                    .without_assignment()
                    .expect("only valid assignment tokens should be passed to assignment"),
                location,
                builder,
            )?;
            ir_target
        } else {
            target.ir_val
        };
        builder
            .ins()
            .store(MemFlags::new(), value.ir_val, ir_target, 0);
        Ok(value)
    }
    fn call(
        &mut self,
        func: FuncCall,
        ctype: Type,
        args: Vec<Expr>,
        location: &Location,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        // TODO: should type checking go here or in parsing?
        let ftype = match ctype {
            Type::Function(ftype) => ftype,
            _ => unreachable!("parser should only allow calling functions"),
        };
        if ftype.varargs {
            unimplemented!("variadic argument calls");
        }
        let compiled_args: Vec<IrValue> = args
            .into_iter()
            .map(|arg| self.compile_expr(arg, builder).map(|val| val.ir_val))
            .collect::<SemanticResult<_>>()?;
        let call = match func {
            FuncCall::Named(func_name) => {
                let func_id: FuncId = match self.scope.get(&func_name) {
                    Some(Id::Function(func_id)) => *func_id,
                    _ => panic!("parser should catch illegal function calls"),
                };
                let func_ref = self.module.declare_func_in_func(func_id, builder.func);
                builder.ins().call(func_ref, compiled_args.as_slice())
            }
            FuncCall::Indirect(callee) => {
                let sig = ftype.signature(location)?;
                let sigref = builder.import_signature(sig);
                builder
                    .ins()
                    .call_indirect(sigref, callee.ir_val, compiled_args.as_slice())
            }
        };
        let ir_val = match builder.inst_results(call).first() {
            // Just a placeholder.
            None => builder.ins().iconst(types::I32, 0),
            Some(ret) => *ret,
        };
        Ok(Value {
            ir_val,
            ir_type: if *ftype.return_type == Type::Void {
                types::INVALID
            } else {
                ftype
                    .return_type
                    .as_ir_type()
                    .expect("parser should only allow legal function types to be called")
            },
            ctype: *ftype.return_type,
        })
    }
    fn store_static(
        &mut self,
        symbol: Symbol,
        init: Option<Initializer>,
        location: Location,
    ) -> SemanticResult<()> {
        let err_closure = |err| Locatable {
            data: err,
            location: location.clone(),
        };
        let linkage = symbol.storage_class.try_into().map_err(err_closure)?;
        let id = self
            .module
            .declare_data(
                &symbol.id,
                linkage,
                !symbol.qualifiers.c_const,
                Some(
                    symbol
                        .ctype
                        .alignof()
                        .map_err(|err| err.to_string())
                        .and_then(|size| {
                            size.try_into().map_err(|_| {
                                format!("align of {} is greater than 256 bytes", symbol.id)
                            })
                        })
                        .map_err(err_closure)?,
                ),
            )
            .map_err(|err| Locatable {
                data: format!("error storing static value: {}", err),
                location: location.clone(),
            })?;

        self.scope.insert(symbol.id, Id::Global(id));

        let mut ctx = DataContext::new();
        if let Some(init) = init {
            let data = init.into_bytes(&symbol.ctype, &location)?;
            ctx.define(data)
        } else {
            ctx.define_zeroinit(
                symbol
                    .ctype
                    .sizeof()
                    .map_err(|err| err_closure(err.to_string()))? as usize,
            )
        };
        self.module.define_data(id, &ctx).map_err(|err| Locatable {
            data: format!("error defining static variable: {}", err),
            location,
        })
    }
    fn if_stmt(
        &mut self,
        condition: Expr,
        body: Stmt,
        otherwise: Option<Box<Stmt>>,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        // If condtion is zero:
        //      If else_block exists, jump to else_block + compile_all
        //      Otherwise, jump to end_block
        //  Otherwise:
        //      Fallthrough to if_body + compile_all
        //      If else_block exists, jump to end_block + compile_all
        //      Otherwise, fallthrough to end_block
        let condition = self.compile_expr(condition, builder)?;
        let (if_body, end_body) = (builder.create_ebb(), builder.create_ebb());
        if let Some(other) = otherwise {
            let else_body = builder.create_ebb();
            builder.ins().brz(condition.ir_val, else_body, &[]);
            builder.ins().jump(if_body, &[]);

            self.switch_to_block(if_body, builder);
            self.compile_stmt(body, builder)?;
            if !self.ebb_has_return {
                builder.ins().jump(end_body, &[]);
            }
            let if_has_return = self.ebb_has_return;

            self.switch_to_block(else_body, builder);
            self.compile_stmt(*other, builder)?;
            if !self.ebb_has_return {
                builder.ins().jump(end_body, &[]);
                // ebb_has_return is already false
                builder.switch_to_block(end_body);
            // if we returned in both 'if' and 'else' blocks, all following code is unreachable
            // this is the case where we returned in 'else' but not 'if'
            } else if !if_has_return {
                self.switch_to_block(end_body, builder);
            }
        } else {
            builder.ins().brz(condition.ir_val, end_body, &[]);
            builder.ins().jump(if_body, &[]);

            self.switch_to_block(if_body, builder);
            self.compile_stmt(body, builder)?;
            if !self.ebb_has_return {
                builder.ins().jump(end_body, &[]);
            }

            self.switch_to_block(end_body, builder);
        };
        Ok(())
    }
    fn while_stmt(
        &mut self,
        condition: Expr,
        maybe_body: Option<Box<Stmt>>,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        let (loop_body, end_body) = (builder.create_ebb(), builder.create_ebb());
        self.loops.push((loop_body, end_body));

        builder.ins().jump(loop_body, &[]);
        self.switch_to_block(loop_body, builder);
        let condition = self.compile_expr(condition, builder)?;
        builder.ins().brz(condition.ir_val, end_body, &[]);

        if let Some(body) = maybe_body {
            self.compile_stmt(*body, builder)?;
        }

        builder.ins().jump(loop_body, &[]);
        self.switch_to_block(end_body, builder);
        self.loops.pop();
        Ok(())
    }
    fn loop_exit(
        &mut self,
        is_break: bool,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        if let Some((loop_start, loop_end)) = self.loops.last() {
            if is_break {
                builder.ins().jump(*loop_end, &[]);
            } else {
                builder.ins().jump(*loop_start, &[]);
            }
            Ok(())
        } else {
            err!(
                format!(
                    "'{}' statement not in loop or switch statement",
                    if is_break { "break" } else { "continue" }
                ),
                location
            );
        }
    }
    #[inline]
    fn switch_to_block(&mut self, ebb: Ebb, builder: &mut FunctionBuilder) {
        builder.switch_to_block(ebb);
        self.ebb_has_return = false;
    }
}

impl Initializer {
    fn into_bytes(self, ctype: &Type, location: &Location) -> SemanticResult<Box<[u8]>> {
        match self {
            Initializer::InitializerList(mut initializers) => match ctype {
                Type::Array(ty, ArrayType::Unbounded) => {
                    let len = initializers.len() as u64;
                    let array_type = Type::Array(ty.clone(), ArrayType::Fixed(len));
                    array_to_bytes(initializers, len, &array_type, ty, location)
                }
                Type::Array(ty, ArrayType::Fixed(size)) => {
                    let size = *size;
                    if initializers.len() as u64 > size {
                        Err(Locatable {
                            data: format!(
                                "too many elements for array (expected {}, got {})",
                                size,
                                initializers.len()
                            ),
                            // TODO: this location points to the declarator, not the initializer
                            location: location.clone(),
                        })
                    } else {
                        array_to_bytes(initializers, size, ctype, ty, location)
                    }
                }
                ty if ty.is_scalar() => {
                    assert_eq!(initializers.len(), 1);
                    initializers.remove(0).into_bytes(ctype, location)
                }
                Type::Union(_) => unimplemented!("union initializers"),
                Type::Struct(_) => unimplemented!("struct initializers"),
                Type::Bitfield(_) => unimplemented!("bitfield initalizers"),

                Type::Function(_) => unreachable!("function initializers"),
                Type::Void => unreachable!("initializer for void type"),
                _ => unreachable!("scalar types should have been handled"),
            },
            Initializer::Scalar(expr) => expr.into_bytes(),
            Initializer::FunctionBody(_) => {
                panic!("function definitions should go through compile_function, not store_static")
            }
        }
    }
}

fn array_to_bytes(
    initializers: Vec<Initializer>,
    len: u64,
    array_type: &Type,
    inner_type: &Type,
    location: &Location,
) -> SemanticResult<Box<[u8]>> {
    if let Type::Array(_, ArrayType::Unbounded) = inner_type {
        err!(
            "nested array must declare the size of each inner array".into(),
            location.clone()
        );
    }
    let init_len = initializers.len();
    let mut bytes = vec![];
    let elements = initializers
        .into_iter()
        .map(|init| init.into_bytes(inner_type, location));

    for init in elements {
        bytes.extend_from_slice(&*init?);
    }
    let sizeof = array_type.sizeof().map_err(|err| Locatable {
        location: location.clone(),
        data: err.to_string(),
    })?;
    let remaining_bytes = sizeof * (len - init_len as u64);
    let mut zero_init = Vec::new();
    zero_init.resize(remaining_bytes as usize, 0);
    bytes.append(&mut zero_init);

    Ok(bytes.into_boxed_slice())
}

impl Expr {
    fn into_bytes(self) -> SemanticResult<Box<[u8]>> {
        match self.constexpr()? {
            Ok(constexpr) => {
                let (token, ctype) = constexpr.data;
                token.into_bytes(&ctype, &constexpr.location)
            }
            Err(location) => Err(Locatable {
                data: "expression is not a compile time constant".into(),
                location,
            }),
        }
    }
}

macro_rules! cast {
    ($i: expr, $from: ty, $to: ty, $ctype: expr, $location: expr) => {{
        let cast = $i as $to;
        if cast as $from != $i {
            warn(
                &format!(
                    "conversion to {} loses precision ({} != {})",
                    $ctype, cast as $from, $i
                ),
                $location,
            )
        }
        cast
    }};
}

macro_rules! bytes {
    ($int: expr, $be: expr) => {{
        let boxed: Box<[u8]> = if $be {
            Box::new($int.to_be_bytes())
        } else {
            Box::new($int.to_le_bytes())
        };
        boxed
    }};
}

impl Token {
    fn into_bytes(self, ctype: &Type, location: &Location) -> SemanticResult<Box<[u8]>> {
        let ir_type = match ctype.as_ir_type() {
            Err(err) => {
                return Err(Locatable {
                    data: err,
                    location: location.clone(),
                })
            }
            Ok(ir_type) => ir_type,
        };
        let big_endian = TARGET
            .endianness()
            .expect("target should be big or little endian")
            == target_lexicon::Endianness::Big;

        match self {
            Token::Int(i) => Ok(match ir_type {
                types::I8 => bytes!(cast!(i, i64, i8, &ctype, &location), big_endian),
                types::I16 => bytes!(cast!(i, i64, i16, &ctype, &location), big_endian),
                types::I32 => bytes!(cast!(i, i64, i32, &ctype, &location), big_endian),
                types::I64 => bytes!(i, big_endian),
                x => unreachable!(format!(
                    "ir_type {} for integer {} is not of integer type",
                    x, i
                )),
            }),
            Token::UnsignedInt(i) => Ok(match ir_type {
                types::I8 => bytes!(cast!(i, u64, u8, &ctype, &location), big_endian),
                types::I16 => bytes!(cast!(i, u64, u16, &ctype, &location), big_endian),
                types::I32 => bytes!(cast!(i, u64, u32, &ctype, &location), big_endian),
                types::I64 => bytes!(i, big_endian),
                x => unreachable!(format!(
                    "ir_type {} for integer {} is not of integer type",
                    x, i
                )),
            }),
            Token::Float(f) => Ok(match ir_type {
                types::F32 => {
                    let cast = f as f32;
                    if (f64::from(cast) - f).abs() >= std::f64::EPSILON {
                        warn(&format!("conversion from double to float loses precision ({} is different from {} by more than DBL_EPSILON ({}))",
                        f64::from(cast), f, std::f64::EPSILON), &location);
                    }
                    let float_as_int = cast.to_bits();
                    bytes!(float_as_int, big_endian)
                }
                types::F64 => bytes!(f.to_bits(), big_endian),
                x => unreachable!(format!(
                    "ir_type {} for float {} is not of integer type",
                    x, f
                )),
            }),
            Token::Str(string) => Ok(string.into_boxed_str().into()),
            Token::Char(c) => Ok(Box::new([c])),
            x => unimplemented!("storing static of type {:?}", x),
        }
    }
}

impl TryFrom<StorageClass> for Linkage {
    type Error = String;
    fn try_from(sc: StorageClass) -> Result<Linkage, String> {
        match sc {
            StorageClass::Extern => Ok(Linkage::Export),
            StorageClass::Static => Ok(Linkage::Local),
            StorageClass::Auto | StorageClass::Register | StorageClass::Typedef => {
                Err(format!("illegal storage class {} for global variable", sc))
            }
        }
    }
}
