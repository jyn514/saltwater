use std::convert::{TryFrom, TryInto};

use inkwell::{
    context::Context,
    module::Linkage,
    module::Module,
    types::{BasicType, BasicTypeEnum, FunctionType as LLVMFunctionType},
    values,
};

use crate::data::{
    Declaration, Expr, FunctionType, Initializer, Locatable, Location, Qualifiers, Stmt,
    StorageClass, Symbol, Type,
};

struct LLVMCompiler {
    context: Context,
    // TODO: allow compiling multiple modules with the same compiler struct?
    module: Module,
    static_init: i64,
    addr: i64,
    reg: i64,
    label: i64,
}

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
    Ok(compiler.module)
}

impl LLVMCompiler {
    fn new() -> LLVMCompiler {
        let context = Context::create();
        LLVMCompiler {
            module: context.create_module("<default-module>"),
            context,
            static_init: 0,
            addr: 0,
            reg: 0,
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
        let params = func_type
            .params
            .into_iter()
            .map(|param| param.ctype.try_into())
            .collect::<Result<Vec<BasicTypeEnum>, _>>()?;
        let llvm_type: LLVMFunctionType =
            BasicTypeEnum::try_from(*func_type.return_type)?.fn_type(&params, func_type.varargs);
        let func = self.module.add_function(&id, llvm_type, Some(linkage));

        let stmts = match init {
            Initializer::CompoundStatement(stmts) => stmts,
            x => panic!("expected compound statement from parser, got '{:#?}'", x),
        };
        self.compile_all(stmts, func);
        Ok(())
    }
    fn compile_all(&mut self, stmts: Vec<Stmt>, func: values::FunctionValue) {
        for stmt in stmts {
            self.compile_stmt(stmt, func);
        }
    }
    fn compile_stmt(&mut self, stmt: Stmt, func: values::FunctionValue) {
        match stmt {
            Stmt::Compound(stmts) => self.compile_all(stmts, func),
            Stmt::If(condition, body, otherwise) => {
                let jmp_if_false = self.label;
                self.label += 1;
                //let reg = self.compile_expr(condition);
            }
            _ => unimplemented!("almost every statement"),
        }
    }
    fn compile_expr(&mut self, expr: Expr) -> Box<values::BasicValue> {
        Box::new(self.context.i64_type().const_zero())
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
