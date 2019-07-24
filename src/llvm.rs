use inkwell::{
    builder::Builder,
    context::Context,
    module::Linkage,
    module::Module,
    types::{BasicType, BasicTypeEnum, FunctionType as LLVMFunctionType},
    values::{BasicValue, BasicValueEnum, FunctionValue},
};

use crate::data::{
    Declaration, Expr, FunctionType, Initializer, Locatable, Location, Qualifiers, Stmt,
    StorageClass, Symbol, Type,
};

struct LLVMCompiler {
    context: Context,
    // TODO: allow compiling multiple modules with the same compiler struct?
    module: Module,
    builder: Builder,
    label: i64,
}

/// Compile a program from a high level IR to an Inkwell Module
pub fn compile(program: Vec<Locatable<Declaration>>) -> Result<Module, Locatable<String>> {
    let mut compiler = LLVMCompiler::new();
    for decl in program {
        if let Some(init) = decl.data.init {
            match decl.data.symbol.ctype {
                Type::Void => panic!("parser let an incomplete type through"),
                Type::Function(func_type) => compiler.compile_func(
                    decl.data.symbol.id,
                    func_type,
                    decl.data.symbol.qualifiers,
                    decl.data.symbol.storage_class,
                    init,
                    decl.location,
                )?,
                _ => compiler.store_static(decl.data.symbol, init, decl.location),
            }
        }
    }
    if let Err(err) = compiler.module.verify() {
        panic!(
            "unknown compile error when generating LLVM bitcode: {}",
            err
        );
    }
    Ok(compiler.module)
}

impl LLVMCompiler {
    fn new() -> LLVMCompiler {
        let context = Context::create();
        let thread = std::thread::current();
        LLVMCompiler {
            module: context.create_module(thread.name().unwrap_or("<default-module>")),
            builder: context.create_builder(),
            context,
            label: 0,
        }
    }
    fn compile_func(
        &mut self,
        id: String,
        func_type: FunctionType,
        quals: Qualifiers,
        sc: StorageClass,
        init: Initializer,
        location: Location,
    ) -> Result<(), Locatable<String>> {
        let linkage = match sc {
            StorageClass::Extern => Linkage::External,
            StorageClass::Static => Linkage::Private,
            StorageClass::Auto | StorageClass::Register => {
                return Err(Locatable {
                    data: format!("illegal storage class {} for function {}", sc, id),
                    location,
                });
            }
        };
        let params = if func_type.params.len() == 1 && func_type.params[0].ctype == Type::Void {
            // no arguments
            Vec::new()
        } else {
            func_type
                .params
                .into_iter()
                .map(|param| {
                    param
                        .ctype
                        .into_llvm_basic(&self.context)
                        .map_err(|err| Locatable {
                            data: err,
                            location: location.clone(),
                        })
                })
                .collect::<Result<Vec<BasicTypeEnum>, Locatable<String>>>()?
        };
        let llvm_type: LLVMFunctionType = func_type
            .return_type
            .into_llvm_basic(&self.context)
            .map_err(|err| Locatable {
                data: err,
                location,
            })?
            .fn_type(&params, func_type.varargs);
        let func = self.module.add_function(&id, llvm_type, Some(linkage));
        let func_start = self.context.append_basic_block(&func, &id);
        self.builder.position_at_end(&func_start);

        let stmts = match init {
            Initializer::CompoundStatement(stmts) => stmts,
            x => panic!("expected compound statement from parser, got '{:#?}'", x),
        };
        self.compile_all(stmts, func);
        Ok(())
    }
    fn compile_all(&mut self, stmts: Vec<Stmt>, func: FunctionValue) {
        for stmt in stmts {
            self.compile_stmt(stmt, func);
        }
    }
    fn compile_stmt(&mut self, stmt: Stmt, func: FunctionValue) {
        match stmt {
            Stmt::Compound(stmts) => self.compile_all(stmts, func),
            Stmt::Return(expr) => {
                let compiled = expr.map(|e| self.compile_expr(e));
                self.builder.build_return(compiled.as_ref().map(|v| v as _));
            }
            Stmt::If(condition, body, otherwise) => {
                let jmp_if_false = self.label;
                self.label += 1;
                //let reg = self.compile_expr(condition);
            }
            _ => unimplemented!("almost every statement"),
        }
    }
    fn compile_expr(&mut self, expr: Expr) -> BasicValueEnum {
        self.context.i32_type().const_zero().as_basic_value_enum()
        //unimplemented!("compiling expressions");
    }
    fn store_static(&mut self, symbol: Symbol, init: Initializer, location: Location) {
        /*
        let mir = Mir::StaticInit(self.addr, init);
        self.addr += 1;
        self.mir.push(mir);
        */
        unimplemented!("static initialization")
    }
}
