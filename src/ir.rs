use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, Type as IrType, Value};
use cranelift_codegen::{
    self as codegen,
    ir::{function::Function, ExternalName, InstBuilder},
    isa,
    settings::{self, Configurable},
};
use cranelift_faerie::{FaerieBackend, FaerieBuilder, FaerieTrapCollection};
use cranelift_module::{self, Linkage, Module as CraneliftModule};

use crate::backend::TARGET;
use crate::data::{
    Declaration, Expr, ExprType, FunctionType, Initializer, Locatable, Location, Qualifiers, Stmt,
    StorageClass, Symbol, Token, Type,
};

type Module = CraneliftModule<FaerieBackend>;

struct LLVMCompiler {
    // TODO: allow compiling multiple modules with the same compiler struct?
    module: Module,
}

/// Compile a program from a high level IR to a Cranelift Module
pub fn compile(program: Vec<Locatable<Declaration>>) -> Result<Module, Locatable<String>> {
    let name = program
        .first()
        .map_or_else(|| "<empty>".to_string(), |decl| decl.data.symbol.id.clone());
    let mut compiler = LLVMCompiler::new(name);
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
    /*
    if let Err(err) = compiler.module.verify() {
        panic!(
            "unknown compile error when generating LLVM bitcode: {}",
            err
        );
    }
    */
    Ok(compiler.module)
}

impl LLVMCompiler {
    fn new(name: String) -> LLVMCompiler {
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
            StorageClass::Extern => Linkage::Export,
            StorageClass::Static => Linkage::Local,
            StorageClass::Auto | StorageClass::Register => {
                return Err(Locatable {
                    data: format!("illegal storage class {} for function {}", sc, id),
                    location,
                });
            }
        };
        let signature = func_type.signature(location)?;
        let func_id = self
            .module
            .declare_function(&id, linkage, &signature)
            .expect("should not have an error declaring a function");
        // external name is meant to be a lookup in a symbol table,
        // but we just give it garbage values
        let mut func = Function::with_name_signature(ExternalName::user(0, 0), signature);

        // this context is just boiler plate
        let mut ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut ctx);

        let func_start = builder.create_ebb();
        builder.append_ebb_params_for_function_params(func_start);
        builder.switch_to_block(func_start);

        let stmts = match init {
            Initializer::CompoundStatement(stmts) => stmts,
            x => panic!("expected compound statement from parser, got '{:#?}'", x),
        };
        self.compile_all(stmts, &mut builder)?;

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
        match stmt {
            Stmt::Compound(stmts) => self.compile_all(stmts, builder)?,
            Stmt::Return(expr) => {
                let mut ret = vec![];
                if let Some(e) = expr {
                    ret.push(self.compile_expr(e, builder)?);
                }
                builder.ins().return_(&ret);
            }
            Stmt::If(condition, body, otherwise) => {
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
    fn compile_expr(
        &mut self,
        expr: Expr,
        builder: &mut FunctionBuilder,
    ) -> Result<Value, Locatable<String>> {
        let location = expr.location;
        let ir_type = expr.ctype.into_llvm_basic().map_err(|err| Locatable {
            data: err,
            location,
        })?;
        match expr.expr {
            ExprType::Literal(token) => self.compile_literal(ir_type, token, builder),
            _ => unimplemented!("any expression other than literals"),
        }
    }
    fn compile_literal(
        &self,
        ir_type: IrType,
        token: Token,
        builder: &mut FunctionBuilder,
    ) -> Result<Value, Locatable<String>> {
        match token {
            Token::Int(i) => Ok(builder.ins().iconst(ir_type, i)),
            Token::Float(f) => Ok(builder.ins().f64const(f)),
            _ => unimplemented!("aggregate literals"),
        }
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
