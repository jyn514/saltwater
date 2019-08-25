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
    types, FunctionBuilder, FunctionBuilderContext, Signature, Type as IrType, Value as IrValue,
};
use cranelift_faerie::{FaerieBackend, FaerieBuilder, FaerieTrapCollection};
use cranelift_module::{self, DataContext, FuncId, Linkage, Module as CraneliftModule};

use crate::backend::TARGET;
use crate::data::{
    prelude::*, ArrayType, FunctionType, Initializer, Qualifiers, Scope, StorageClass,
};
use crate::utils::warn;

type Module = CraneliftModule<FaerieBackend>;
type IrResult = Result<Value, Locatable<String>>;

enum Id {
    Function(FuncId),
    Data(StackSlot),
}

struct LLVMCompiler {
    module: Module,
    ebb_has_return: bool,
    scope: Scope<String, Id>,
    debug: bool,
}

#[derive(Debug, PartialEq, Eq)]
struct Value {
    ir_val: IrValue,
    ir_type: IrType,
    ctype: Type,
}

/// Compile a program from a high level IR to a Cranelift Module
pub(crate) fn compile(
    program: Vec<Locatable<Declaration>>,
    debug: bool,
) -> Result<Module, Locatable<String>> {
    let name = program
        .first()
        .map_or_else(|| "<empty>".to_string(), |decl| decl.data.symbol.id.clone());
    let mut compiler = LLVMCompiler::new(name, debug);
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
            (ty, None) => unimplemented!("data declarations without initializers"),
            (Type::Function(func_type), Some(Initializer::FunctionBody(stmts))) => compiler
                .compile_func(
                    decl.data.symbol.id,
                    func_type,
                    decl.data.symbol.qualifiers,
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

impl LLVMCompiler {
    fn new(name: String, debug: bool) -> LLVMCompiler {
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

        LLVMCompiler {
            module: Module::new(builder),
            ebb_has_return: false,
            scope: Scope::new(),
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
    ) -> Result<FuncId, Locatable<String>> {
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
    ) -> Result<(), Locatable<String>> {
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
        self.scope.insert(decl.symbol.id, Id::Data(stack_slot));
        if let Some(init) = decl.init {
            self.store_stack(init, stack_slot, decl.symbol.ctype, location, builder)?;
        }
        Ok(())
    }
    fn store_stack(
        &self,
        init: Initializer,
        stack_slot: StackSlot,
        ctype: Type,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> Result<(), Locatable<String>> {
        match init {
            Initializer::Scalar(expr) => {
                let val = self.compile_expr(expr, builder)?;
                builder.ins().stack_store(val.ir_val, stack_slot, 0);
            }
            Initializer::InitializerList(_) => unimplemented!("aggregate dynamic initialization"),
            Initializer::FunctionBody(_) => unreachable!("functions can't be stored on the stack"),
        }
        Ok(())
    }
    fn compile_func(
        &mut self,
        id: String,
        func_type: FunctionType,
        quals: Qualifiers,
        sc: StorageClass,
        stmts: Vec<Stmt>,
        location: Location,
    ) -> Result<(), Locatable<String>> {
        let signature = func_type.signature(&location)?;
        let func_id = self.declare_func(id, &signature, sc, &location, false)?;
        // external name is meant to be a lookup in a symbol table,
        // but we just give it garbage values
        let mut func = Function::with_name_signature(ExternalName::user(0, 0), signature);

        // this context is just boiler plate
        let mut ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut ctx);

        let func_start = builder.create_ebb();
        builder.append_ebb_params_for_function_params(func_start);
        builder.switch_to_block(func_start);
        self.ebb_has_return = false;

        self.compile_all(stmts, &mut builder)?;
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
    ) -> Result<(), Locatable<String>> {
        for stmt in stmts {
            self.compile_stmt(stmt, builder)?;
        }
        Ok(())
    }
    fn compile_stmt(
        &mut self,
        stmt: Stmt,
        builder: &mut FunctionBuilder,
    ) -> Result<(), Locatable<String>> {
        if self.ebb_has_return {
            return Err(Locatable {
                data: "unreachable statement".into(),
                // TODO: this location is not even trying
                location: Default::default(),
            });
        }
        match stmt.data {
            StmtType::Compound(stmts) => self.compile_all(stmts, builder)?,
            // INVARIANT: symbol has not yet been declared in this scope
            StmtType::Decl(decl) => self.declare_data(*decl, stmt.location, builder)?,
            StmtType::Expr(expr) => {
                self.compile_expr(expr, builder)?;
            }
            StmtType::Return(expr) => {
                let mut ret = vec![];
                if let Some(e) = expr {
                    let val = self.compile_expr(e, builder)?;
                    ret.push(val.ir_val);
                }
                self.ebb_has_return = true;
                builder.ins().return_(&ret);
            }
            StmtType::If(condition, body, otherwise) => {
                // If condtion is zero:
                //      If else_block exists, jump to else_block + compile_all
                //      Otherwise, jump to end_block
                //  Otherwise:
                //      Fallthrough to if_body + compile_all
                //      If else_block exists, jump to end_block + compile_all
                //      Otherwise, fallthrough to end_block
                /*
                let condition = self.compile_expr(condition);
                let (if_body, end_body) = (builder.create_ebb(), builder.create_ebb());
                let target = if let Some(o) = otherwise {
                    let else_body = builder.create_ebb();
                    builder.switch_to_block(else_body);
                    self.compile_all(o, builder);
                    builder.switch_to_block(
                    else_body
                } else {
                    end_body
                };
                builder.ins().brz(condtion, target, &[]);
                */
                unimplemented!("if statements");
                //let reg = self.compile_expr(condition);
            }
            _ => unimplemented!("almost every statement"),
        };
        Ok(())
    }
    // clippy doesn't like big match statements, but this is kind of essential complexity,
    // it can't be any smaller without supporting fewer features
    #[allow(clippy::cognitive_complexity)]
    fn compile_expr(&self, expr: Expr, builder: &mut FunctionBuilder) -> IrResult {
        let expr = expr.const_fold()?;
        let location = expr.location;
        let ir_type = match expr.ctype.as_ir_basic_type() {
            Ok(ir_type) => ir_type,
            Err(err) => {
                return Err(Locatable {
                    data: err,
                    location,
                });
            }
        };
        match expr.expr {
            ExprType::Literal(token) => self.compile_literal(ir_type, expr.ctype, token, builder),
            ExprType::Id(var) => self.load_addr(var, location, builder),

            // unary operators
            // NOTE: this may be an implicit cast (float f = 1.2) not an explicit cast (1 + (int)1.2)
            // NOTE: it may also be a widening conversion (1 + 1.2)
            ExprType::Deref(pointer) => {
                let val = self.compile_expr(*pointer, builder)?;
                let flags = MemFlags::new();
                Ok(Value {
                    ir_type,
                    ctype: expr.ctype,
                    ir_val: builder.ins().load(val.ir_type, flags, val.ir_val, 0),
                })
            }
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
                ExprType::Id(var) => self.call_direct(var.id, func.ctype, args, location, builder),
                _ => unimplemented!("indirect function calls"),
            },
            ExprType::Comma(left, right) => {
                self.compile_expr(*left, builder)?;
                self.compile_expr(*right, builder)
            }
            x => {
                unimplemented!("{:?}", x);
            }
        }
    }
    fn compile_literal(
        &self,
        ir_type: IrType,
        ctype: Type,
        token: Token,
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
            _ => unimplemented!("aggregate literals"),
        };
        Ok(Value {
            ir_val,
            ir_type,
            ctype,
        })
    }
    fn unary_op<F>(&self, expr: Expr, builder: &mut FunctionBuilder, func: F) -> IrResult
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
        &self,
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
        assert_eq!(left.ir_type, right.ir_type);
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
        let ir_type = ctype
            .as_ir_basic_type()
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
            (Token::Ampersand, ty, true) if ty.is_int() => b::band,
            (Token::BitwiseOr, ty, true) if ty.is_int() => b::bor,
            (Token::ShiftLeft, ty, _) if ty.is_int() => b::ishl,
            // arithmetic shift: keeps the sign of `left`
            (Token::ShiftRight, ty, true) if ty.is_int() => b::sshr,
            // logical shift: shifts in zeros
            (Token::ShiftRight, ty, false) if ty.is_int() => b::ushr,
            (Token::Xor, ty, _) if ty.is_int() => b::bxor,
            _ => unreachable!("only valid assign binary ops should be passed to binary_assign_op"),
        };
        let ir_val = func(builder.ins(), left.ir_val, right.ir_val);
        Ok(Value {
            ir_val,
            ir_type,
            ctype,
        })
    }
    fn cast(
        &self,
        expr: Expr,
        ctype: Type,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        // calculate this here before it's moved to `compile_expr`
        let orig_signed = expr.ctype.is_signed();
        let original = self.compile_expr(expr, builder)?;
        let cast_type = ctype.as_ir_basic_type().map_err(|err| Locatable {
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
                if from_signed {
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
    fn logical_not(&self, expr: Expr, builder: &mut FunctionBuilder) -> IrResult {
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
    fn negate(&self, expr: Expr, builder: &mut FunctionBuilder) -> IrResult {
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
        match self.scope.get(&var.id).unwrap() {
            Id::Function(func_id) => unimplemented!("address of function"),
            Id::Data(stack_slot) => {
                let ir_type = var
                    .ctype
                    .as_ir_basic_type()
                    .map_err(|data| Locatable { data, location })?;
                Ok(Value {
                    ir_type,
                    ir_val: builder.ins().stack_addr(ir_type, *stack_slot, 0),
                    ctype: var.ctype,
                })
            }
        }
    }
    fn compare(
        &self,
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
        &self,
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
                target.ir_val =
                    builder
                        .ins()
                        .load(target.ir_type, MemFlags::new(), target.ir_val, 0);
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
    fn call_direct(
        &self,
        func_name: String,
        ctype: Type,
        args: Vec<Expr>,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        // TODO: should type checking go here or in parsing?
        let ret_type = match ctype {
            Type::Function(FunctionType { return_type, .. }) => *return_type,
            _ => unreachable!("parser should only allow calling functions"),
        };
        let compiled_args: Vec<IrValue> = args
            .into_iter()
            .map(|arg| self.compile_expr(arg, builder).map(|val| val.ir_val))
            .collect::<Result<_, Locatable<String>>>()?;
        // TODO: need access to current scope for this to work
        let func_id: FuncId = match self.scope.get(&func_name) {
            Some(Id::Function(func_id)) => *func_id,
            _ => panic!("parser should catch illegal function calls"),
        };
        let func_ref = self.module.declare_func_in_func(func_id, builder.func);
        let call = builder.ins().call(func_ref, compiled_args.as_slice());
        let ir_val = builder.inst_results(call)[0];
        Ok(Value {
            ir_val,
            ir_type: ret_type
                .as_ir_type()
                .expect("parser should only allow legal function types to be called"),
            ctype: ret_type,
        })
    }
    fn store_static(
        &mut self,
        symbol: Symbol,
        init: Option<Initializer>,
        location: Location,
    ) -> Result<(), Locatable<String>> {
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
                symbol.qualifiers.c_const,
                Some(
                    symbol
                        .ctype
                        .alignof()
                        .map_err(|err| err.to_string())
                        .and_then(|size| {
                            size.try_into().map_err(|f| {
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
}

impl Initializer {
    fn into_bytes(self, ctype: &Type, location: &Location) -> Result<Box<[u8]>, Locatable<String>> {
        match self {
            Initializer::InitializerList(mut initializers) => match ctype {
                Type::Array(ty, ArrayType::Unbounded) => {
                    unimplemented!("inferring size of unbounded array from initializer")
                }
                Type::Array(ty, ArrayType::Fixed(size)) => {
                    let size = *size;
                    if initializers.len() as u64 > size {
                        Err(Locatable {
                            data: format!(
                                "too many initalizers for array (expected {}, got {})",
                                size,
                                initializers.len()
                            ),
                            location: location.clone(),
                        })
                    } else {
                        let init_len = initializers.len();
                        let mut bytes = vec![];
                        let elements = initializers
                            .into_iter()
                            .map(|init| init.into_bytes(ctype, location));

                        for init in elements {
                            bytes.extend_from_slice(&*init?);
                        }
                        let sizeof = ty.sizeof().map_err(|err| Locatable {
                            location: location.clone(),
                            data: err.to_string(),
                        })?;
                        let remaining_bytes = sizeof * (size - init_len as u64);
                        let mut zero_init = Vec::new();
                        zero_init.resize(remaining_bytes as usize, 0);
                        bytes.append(&mut zero_init);

                        Ok(bytes.into_boxed_slice())
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

impl Expr {
    fn into_bytes(self) -> Result<Box<[u8]>, Locatable<String>> {
        match self.constexpr()? {
            Ok(constexpr) => {
                let ctype = constexpr.data.ctype().unwrap();
                constexpr.data.into_bytes(ctype, &constexpr.location)
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
    fn into_bytes(self, ctype: Type, location: &Location) -> Result<Box<[u8]>, Locatable<String>> {
        let ir_type = match ctype.clone().as_ir_basic_type() {
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
