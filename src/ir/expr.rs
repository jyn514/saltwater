use cranelift::codegen::ir::{condcodes, types, MemFlags};
use cranelift::prelude::{FunctionBuilder, InstBuilder, Type as IrType, Value as IrValue};
use cranelift_module::Backend;
use target_lexicon::Triple;

use super::{Compiler, Id};
use crate::data::*;
use crate::data::{
    hir::{BinaryOp, Expr, ExprType, Metadata, MetadataRef},
    lex::{ComparisonToken, Literal},
};

type IrResult = CompileResult<Value>;

#[derive(Clone, Debug, PartialEq)]
pub(super) struct Value {
    pub(super) ir_val: IrValue,
    ir_type: IrType,
    ctype: Type,
}

enum FuncCall {
    Named(MetadataRef),
    Indirect(Value),
}

impl<B: Backend> Compiler<B> {
    // clippy doesn't like big match statements, but this is kind of essential complexity,
    // it can't be any smaller without supporting fewer features
    #[allow(clippy::cognitive_complexity)]
    pub(super) fn compile_expr(&mut self, expr: Expr, builder: &mut FunctionBuilder) -> IrResult {
        let expr = expr.const_fold(&self.target)?;
        let location = expr.location;
        let ir_type = if expr.lval {
            Type::ptr_type(&self.target)
        } else {
            expr.ctype.as_ir_type(&self.target)
        };
        match expr.expr {
            ExprType::Literal(token) => {
                self.compile_literal(ir_type, expr.ctype, token, location, builder)
            }
            ExprType::Id(var) => self.load_addr(var, builder),

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
            ExprType::Cast(orig) => self.cast(*orig, expr.ctype, builder),
            ExprType::Negate(expr) => self.negate(*expr, builder),
            ExprType::BitwiseNot(expr) => self.unary_op(
                *expr,
                builder,
                |ir_val, ir_type, _, builder| match ir_type {
                    ty if ty.is_int() => builder.ins().bnot(ir_val),
                    _ => unreachable!("parser should catch illegal types"),
                },
            ),
            // binary operators
            ExprType::Binary(BinaryOp::LogicalOr, left, right) => {
                self.logical_expr(*left, *right, false, builder)
            }
            ExprType::Binary(BinaryOp::LogicalAnd, left, right) => {
                self.logical_expr(*left, *right, true, builder)
            }
            ExprType::Binary(BinaryOp::Assign, left, right) => {
                self.assignment(*left, *right, builder)
            }
            ExprType::Binary(op, left, right) => {
                self.binary_assign_op(*left, *right, expr.ctype, op, builder)
            }
            ExprType::FuncCall(func, args) => match func.expr {
                ExprType::Id(var) => self.call(FuncCall::Named(var), func.ctype, args, builder),
                _ => {
                    let ctype = func.ctype.clone();
                    let val = self.compile_expr(*func, builder)?;
                    self.call(FuncCall::Indirect(val), ctype, args, builder)
                }
            },
            ExprType::Comma(left, right) => {
                self.compile_expr(*left, builder)?;
                self.compile_expr(*right, builder)
            }
            ExprType::Member(cstruct, id) => {
                let ctype = cstruct.ctype.clone();
                let pointer = self.compile_expr(*cstruct, builder)?;
                let offset = ctype
                    .member_offset(id, &self.target)
                    .expect("only structs and unions can have members");
                let ir_offset = builder
                    .ins()
                    .iconst(Type::ptr_type(&self.target), offset as i64);
                Ok(Value {
                    ir_val: builder.ins().iadd(pointer.ir_val, ir_offset),
                    ir_type,
                    ctype,
                })
            }
            ExprType::PostIncrement(lval, increase) => {
                let lval = self.compile_expr(*lval, builder)?;
                let loaded_ctype = match lval.ctype {
                    Type::Pointer(t, _) => *t,
                    _ => lval.ctype,
                };
                let ir_type = loaded_ctype.as_ir_type(&self.target);
                let previous_value = Value {
                    ir_val: builder.ins().load(ir_type, MemFlags::new(), lval.ir_val, 0),
                    ir_type,
                    ctype: loaded_ctype,
                };

                let addend = if increase { 1 } else { -1 };
                let (addend_ir, add_func): (_, fn(_, _, _) -> _) = match previous_value.ctype {
                    Type::Double => (builder.ins().f64const(addend as f64), InstBuilder::fadd),
                    Type::Float => (builder.ins().f32const(addend as f32), InstBuilder::fadd),
                    _ => (
                        builder.ins().iconst(previous_value.ir_type, addend),
                        InstBuilder::iadd,
                    ),
                };
                let new_value = add_func(builder.ins(), previous_value.ir_val, addend_ir);
                builder
                    .ins()
                    .store(MemFlags::new(), new_value, lval.ir_val, 0);
                Ok(previous_value)
            }
            ExprType::Noop(inner) => {
                let mut val = self.compile_expr(*inner, builder)?;
                val.ctype = expr.ctype;
                Ok(val)
            }
            ExprType::Ternary(condition, left, right) => {
                self.ternary(*condition, *left, *right, builder)
            }
            ExprType::Sizeof(_) => unimplemented!("sizeof variable length arrays"),
            ExprType::StaticRef(_) => {
                unreachable!("static refs can only appear in top level declarations")
            }
        }
    }
    fn ternary(
        &mut self,
        condition: Expr,
        left: Expr,
        right: Expr,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        let target_block = builder.create_block();
        let target_type = left.ctype.as_ir_type(&self.target);
        builder.append_block_param(target_block, target_type);

        let condition = self.compile_expr(condition, builder)?;
        let (block_if_true, block_if_false) = (builder.create_block(), builder.create_block());
        builder.ins().brnz(condition.ir_val, block_if_true, &[]);
        builder.ins().jump(block_if_false, &[]);

        builder.switch_to_block(block_if_true);
        let left_val = self.compile_expr(left, builder)?;
        builder.ins().jump(target_block, &[left_val.ir_val]);

        builder.switch_to_block(block_if_false);
        let right_val = self.compile_expr(right, builder)?;
        builder.ins().jump(target_block, &[right_val.ir_val]);
        builder.switch_to_block(target_block);

        Ok(Value {
            ir_val: *builder.block_params(target_block).first().unwrap(),
            ir_type: target_type,
            ctype: left_val.ctype,
        })
    }
    fn logical_expr(
        &mut self,
        left: Expr,
        right: Expr,
        brz: bool,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        let target_block = builder.create_block();
        builder.append_block_param(target_block, types::B1);
        let left = self.compile_expr(left, builder)?;

        let branch_func = if brz {
            InstBuilder::brz
        } else {
            InstBuilder::brnz
        };
        branch_func(builder.ins(), left.ir_val, target_block, &[left.ir_val]);
        self.fallthrough(builder);

        let right = self.compile_expr(right, builder)?;
        builder.ins().jump(target_block, &[right.ir_val]);

        builder.switch_to_block(target_block);
        Ok(Value {
            ir_val: *builder
                .block_params(target_block)
                .first()
                .expect("if we passed an block arg it should be here"),
            ir_type: types::B1,
            ctype: Type::Bool,
        })
    }
    fn compile_literal(
        &mut self,
        ir_type: IrType,
        ctype: Type,
        token: Literal,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        let ir_val = match (token, ir_type) {
            (Literal::Int(i), types::B1) => builder.ins().bconst(ir_type, i != 0),
            (Literal::Int(i), _) => builder.ins().iconst(ir_type, i),
            (Literal::UnsignedInt(u), types::B1) => builder.ins().bconst(ir_type, u != 0),
            (Literal::UnsignedInt(u), _) => builder.ins().iconst(ir_type, u as i64),
            (Literal::Float(f), types::F32) => builder.ins().f32const(f as f32),
            (Literal::Float(f), types::F64) => builder.ins().f64const(f),
            (Literal::Char(c), _) => builder.ins().iconst(ir_type, i64::from(c)),
            (Literal::Str(string), _) => {
                let str_id = self.compile_string(string, location)?;
                let str_addr = self.module.declare_data_in_func(str_id, builder.func);
                builder
                    .ins()
                    .global_value(Type::ptr_type(&self.target), str_addr)
            }
            _ => unimplemented!("aggregate literals"),
        };
        Ok(Value {
            ir_val,
            ir_type,
            ctype,
        })
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
        op: BinaryOp,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        let (left, right) = (
            self.compile_expr(left, builder)?,
            self.compile_expr(right, builder)?,
        );
        Self::binary_assign_ir(left, right, ctype, op, &self.target, builder)
    }
    fn binary_assign_ir(
        left: Value,
        right: Value,
        ctype: Type,
        op: BinaryOp,
        target: &Triple,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        use cranelift::codegen::ir::InstBuilder as b;
        use BinaryOp::*;
        assert_eq!(left.ir_type, right.ir_type);
        let ir_type = ctype.as_ir_type(&target);
        let signed = ctype.is_signed();
        let func = match (op, ir_type, signed) {
            (Add, ty, _) if ty.is_int() => b::iadd,
            (Add, ty, _) if ty.is_float() => b::fadd,
            (Sub, ty, _) if ty.is_int() => b::isub,
            (Sub, ty, _) if ty.is_float() => b::fsub,
            (Mul, ty, _) if ty.is_int() => b::imul,
            (Mul, ty, _) if ty.is_float() => b::fmul,
            (Div, ty, true) if ty.is_int() => b::sdiv,
            (Div, ty, false) if ty.is_int() => b::udiv,
            (Div, ty, _) if ty.is_float() => b::fdiv,
            (Mod, ty, true) if ty.is_int() => b::srem,
            (Mod, ty, false) if ty.is_int() => b::urem,
            (BitwiseAnd, ty, _) if ty.is_int() || ty.is_bool() => b::band,
            (BitwiseOr, ty, _) if ty.is_int() || ty.is_bool() => b::bor,
            (Shl, ty, _) if ty.is_int() => b::ishl,
            // arithmetic shift: keeps the sign of `left`
            (Shr, ty, true) if ty.is_int() => b::sshr,
            // logical shift: shifts in zeros
            (Shr, ty, false) if ty.is_int() => b::ushr,
            (Xor, ty, _) if ty.is_int() => b::bxor,
            (Compare(token), _, _) => return Self::compare(left, right, token, builder),
            (Assign, _, _) | (LogicalAnd, _, _) | (LogicalOr, _, _) => {
                unreachable!("should be handled earlier")
            }
            _ => unreachable!(
                "bug in parser: passed invalid type {} for binary op {}",
                ctype, op
            ),
        };
        let ir_val = func(builder.ins(), left.ir_val, right.ir_val);
        Ok(Value {
            ir_val,
            ir_type,
            ctype,
        })
    }
    fn cast(&mut self, expr: Expr, ctype: Type, builder: &mut FunctionBuilder) -> IrResult {
        // calculate this here before it's moved to `compile_expr`
        let orig_signed = expr.ctype.is_signed();
        let original = self.compile_expr(expr, builder)?;
        if ctype == Type::Void {
            // this cast is a no-op, it's just here for the frontend
            return Ok(original);
        }
        let cast_type = ctype.as_ir_type(&self.target);
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
                if from_signed {
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
    fn negate(&mut self, expr: Expr, builder: &mut FunctionBuilder) -> IrResult {
        self.unary_op(expr, builder, |ir_val, ir_type, _, builder| match ir_type {
            i if i.is_int() => builder.ins().irsub_imm(ir_val, 0),
            f if f.is_float() => builder.ins().fneg(ir_val),
            _ => unreachable!("parser should catch illegal types"),
        })
    }
    fn load_addr(&self, var: MetadataRef, builder: &mut FunctionBuilder) -> IrResult {
        let metadata = var.get();
        let ptr_type = Type::ptr_type(&self.target);
        let ir_val = match self
            .declarations
            .get(&var)
            .expect("bug in parser: loaded a variable that was not declared")
        {
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
        let ctype = Type::Pointer(Box::new(metadata.ctype.clone()), hir::Qualifiers::default());
        Ok(Value {
            ir_type: ptr_type,
            ir_val,
            ctype,
        })
    }
    fn compare(
        left: Value,
        right: Value,
        token: ComparisonToken,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        assert_eq!(left.ir_type, right.ir_type);

        let ir_val = if left.ir_type.is_int() {
            let code = token.to_int_compare(left.ctype.is_signed());
            builder.ins().icmp(code, left.ir_val, right.ir_val)
        } else if left.ir_type.is_bool() {
            let left = builder.ins().bint(types::I8, left.ir_val);
            let right = builder.ins().bint(types::I8, right.ir_val);
            let code = token.to_int_compare(false);
            builder.ins().icmp(code, left, right)
        } else {
            assert!(left.ir_type.is_float());
            let code = token.to_float_compare();
            builder.ins().fcmp(code, left.ir_val, right.ir_val)
        };
        Ok(Value {
            ir_val,
            ir_type: types::B1,
            ctype: left.ctype,
        })
    }
    fn assignment(&mut self, lval: Expr, rval: Expr, builder: &mut FunctionBuilder) -> IrResult {
        let ctype = lval.ctype.clone();
        let location = lval.location;
        let (target, value) = (
            self.compile_expr(lval, builder)?,
            self.compile_expr(rval, builder)?,
        );
        if let Type::Union(_) | Type::Struct(_) = ctype {
            use std::convert::TryInto;
            let size = ctype
                .sizeof(&self.target)
                .map_err(|e| location.with(e.to_string()))?;
            let align = ctype
                .alignof(&self.target)
                .expect("if sizeof(&self.target) succeeds so should alignof()")
                .try_into()
                .expect("align should never be more than 255 bytes");
            builder.emit_small_memory_copy(
                self.module.target_config(),
                target.ir_val,
                value.ir_val,
                size,
                align,
                align,
                // could be overlapping: `s = s;`
                false,
            );
            return Ok(value);
        }
        // scalar assignment
        let target_val = target.ir_val;
        builder
            .ins()
            .store(MemFlags::new(), value.ir_val, target_val, 0);
        Ok(value)
    }
    fn call(
        &mut self,
        func: FuncCall,
        ctype: Type,
        args: Vec<Expr>,
        builder: &mut FunctionBuilder,
    ) -> IrResult {
        use crate::data::hir::Qualifiers;
        use cranelift::codegen::ir::{AbiParam, ArgumentPurpose};

        let mut ftype = match ctype {
            Type::Function(ftype) => ftype,
            _ => unreachable!("parser should only allow calling functions"),
        };
        let mut float_variadic = 0;
        if ftype.varargs {
            // needs to be done before we move the args by compiling them
            if self.module.isa().name() != "x86" {
                unimplemented!("variadic args for architectures other than x86");
            }
            // this is an utter hack
            // https://github.com/CraneStation/cranelift/issues/212#issuecomment-549111736
            for arg in &args[ftype.params.len()..] {
                if arg.ctype.is_floating() {
                    float_variadic += 1;
                }
                ftype.params.push(
                    Metadata {
                        ctype: arg.ctype.clone(),
                        id: Default::default(),
                        qualifiers: Qualifiers::NONE,
                        storage_class: StorageClass::Auto,
                    }
                    .insert(),
                );
            }
        }
        let mut compiled_args: Vec<IrValue> = args
            .into_iter()
            .map(|arg| self.compile_expr(arg, builder).map(|val| val.ir_val))
            .collect::<CompileResult<_>>()?;
        if ftype.varargs {
            let float_ir = builder.ins().iconst(types::I8, float_variadic);
            compiled_args.push(float_ir);
        }
        let call = match func {
            FuncCall::Named(func_name) => {
                let func_id = match self.declarations.get(&func_name) {
                    Some(Id::Function(func_id)) => *func_id,
                    _ => panic!("parser should catch illegal function calls"),
                };
                let func_ref = self.module.declare_func_in_func(func_id, builder.func);
                let call = builder.ins().call(func_ref, compiled_args.as_slice());
                // stolen from https://github.com/bjorn3/rustc_codegen_cranelift/blob/82fde5b62281fa51a/src/abi/mod.rs#L535
                if ftype.varargs {
                    let call_sig = builder.func.dfg.call_signature(call).unwrap();
                    let al = self
                        .module
                        .isa()
                        .register_info()
                        .parse_regunit("rax")
                        .expect("x86 should have an rax register");
                    let float_arg = AbiParam::special_reg(types::I8, ArgumentPurpose::Normal, al);
                    // NOTE: this is added both here and in signature() because we overwrite the previous params
                    let abi_params = ftype
                        .params
                        .into_iter()
                        .map(|param| AbiParam::new(param.get().ctype.as_ir_type(&self.target)))
                        .chain(std::iter::once(float_arg))
                        .collect();
                    builder.func.dfg.signatures[call_sig].params = abi_params;
                }
                call
            }
            FuncCall::Indirect(callee) => {
                let sig = ftype.signature(self.module.isa(), &self.target);
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
            ir_type: ftype.return_type.as_ir_type(&self.target),
            ctype: *ftype.return_type,
        })
    }
}
