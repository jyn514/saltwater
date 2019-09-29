mod expr;
mod static_init;
mod stmt;

use std::convert::{TryFrom, TryInto};

use cranelift::codegen::{
    self,
    ir::{
        entities::StackSlot,
        function::Function,
        stackslot::{StackSlotData, StackSlotKind},
        ExternalName, InstBuilder, MemFlags,
    },
    isa,
    settings::{self, Configurable},
};
use cranelift::frontend::Switch;
use cranelift::prelude::{Ebb, FunctionBuilder, FunctionBuilderContext, Signature};
use cranelift_faerie::{FaerieBackend, FaerieBuilder, FaerieTrapCollection};
use cranelift_module::{self, DataId, FuncId, Linkage, Module as CraneliftModule};

use crate::backend::TARGET;
use crate::data::{prelude::*, types::FunctionType, Initializer, Scope, StorageClass};

type Module = CraneliftModule<FaerieBackend>;

#[derive(Debug)]
enum Id {
    Function(FuncId),
    Global(DataId),
    Local(StackSlot),
}

struct Compiler {
    module: Module,
    scope: Scope<String, Id>,
    debug: bool,
    // if false, we last saw a switch
    last_saw_loop: bool,
    str_index: usize,
    loops: Vec<(Ebb, Ebb)>,
    // switch, default, end
    // if default is empty once we get to the end of a switch body,
    // we didn't see a default case
    switches: Vec<(Switch, Option<Ebb>, Ebb)>,
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
                if func_type.params.is_empty() {
                    continue; // function without prototype, don't pass it to cranelift
                }
                compiler.declare_func(
                    decl.data.symbol.id,
                    &func_type.signature(),
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
        // minimal optimizations
        flags_builder
            .set("opt_level", "speed")
            .expect("opt_level: speed should be a valid option");

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
            scope: Scope::new(),
            loops: Vec::new(),
            switches: Vec::new(),
            // the initial value doesn't really matter
            last_saw_loop: true,
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
    fn declare_stack(
        &mut self,
        decl: Declaration,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        if let Type::Function(ftype) = decl.symbol.ctype {
            self.declare_func(
                decl.symbol.id,
                &ftype.signature(),
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
            self.store_stack(init, stack_slot, builder)?;
        }
        Ok(())
    }
    fn store_stack(
        &mut self,
        init: Initializer,
        stack_slot: StackSlot,
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
                let ir_type = param.ctype.as_ir_type();
                Ok(builder.append_ebb_param(func_start, ir_type))
            })
            .collect::<Result<_, Locatable<String>>>()?;
        for (param, ir_val) in params.into_iter().zip(ir_vals) {
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
        let signature = func_type.signature();
        let func_id = self.declare_func(id.clone(), &signature, sc, &location, false)?;
        // external name is meant to be a lookup in a symbol table,
        // but we just give it garbage values
        let mut func = Function::with_name_signature(ExternalName::user(0, 0), signature);

        // this context is just boiler plate
        let mut ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut ctx);

        let func_start = builder.create_ebb();
        builder.switch_to_block(func_start);

        let should_ret = func_type.should_return();
        if func_type.has_params() {
            self.store_stack_params(func_type.params, func_start, &location, &mut builder)?;
        }
        self.compile_all(stmts, &mut builder)?;
        if !builder.is_filled() {
            if id == "main" {
                let ir_int = func_type.return_type.as_ir_type();
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
}
