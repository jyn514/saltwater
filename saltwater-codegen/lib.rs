/// Return an error from a function
/// Assumes that 'Locatable' is in scope and that the function it is called in
/// returns a 'Result<Locatable<T>>'
macro_rules! semantic_err {
    ($message: expr, $location: expr $(,)?) => {
        return Err(CompileError::semantic(Locatable {
            data: $message,
            location: $location,
        }));
    };
}

mod expr;
mod static_init;
mod stmt;

use std::collections::HashMap;
use std::convert::TryFrom;
use std::path::Path;

use cranelift::codegen::{
    self,
    ir::{
        entities::StackSlot,
        function::Function,
        stackslot::{StackSlotData, StackSlotKind},
        ExternalName, InstBuilder, MemFlags,
    },
    isa::TargetIsa,
    settings::{self, Configurable, Flags},
};
use cranelift::frontend::Switch;
use cranelift::prelude::{Block, FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{self, Backend, DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBackend, ObjectBuilder};
use saltwater_parser::arch::TARGET;
use saltwater_parser::{Opt, Program};

use saltwater_parser::data::{
    hir::{Declaration, Initializer, Stmt, Symbol},
    types::FunctionType,
    StorageClass, *,
};

pub(crate) fn get_isa(jit: bool) -> Box<dyn TargetIsa + 'static> {
    let mut flags_builder = cranelift::codegen::settings::builder();
    // `simplejit` requires non-PIC code
    if !jit {
        // allow creating shared libraries
        flags_builder
            .enable("is_pic")
            .expect("is_pic should be a valid option");
    }
    // use debug assertions
    flags_builder
        .enable("enable_verifier")
        .expect("enable_verifier should be a valid option");
    // don't emit call to __cranelift_probestack
    flags_builder
        .set("enable_probestack", "false")
        .expect("enable_probestack should be a valid option");
    let flags = Flags::new(flags_builder);
    cranelift::codegen::isa::lookup(TARGET)
        .unwrap_or_else(|_| panic!("platform not supported: {}", TARGET))
        .finish(flags)
}

pub fn initialize_aot_module(name: String) -> Module<ObjectBackend> {
    let builder = ObjectBuilder::new(
        get_isa(false),
        name,
        cranelift_module::default_libcall_names(),
    );
    Module::new(builder.expect("unsupported binary format or target architecture"))
}

enum Id {
    Function(FuncId),
    Global(DataId),
    Local(StackSlot),
}

struct Compiler<T: Backend> {
    module: Module<T>,
    debug: bool,
    // if false, we last saw a switch
    last_saw_loop: bool,
    strings: HashMap<Vec<u8>, DataId>,
    declarations: HashMap<Symbol, Id>,
    loops: Vec<(Block, Block)>,
    // switch, default, end
    // if default is empty once we get to the end of a switch body,
    // we didn't see a default case
    switches: Vec<(Switch, Option<Block>, Block)>,
    labels: HashMap<InternedStr, Block>,
    error_handler: ErrorHandler,
}

impl<B: Backend> Compiler<B> {
    fn new(module: Module<B>, debug: bool) -> Compiler<B> {
        Compiler {
            module,
            declarations: HashMap::new(),
            loops: Vec::new(),
            switches: Vec::new(),
            labels: HashMap::new(),
            // the initial value doesn't really matter
            last_saw_loop: true,
            strings: Default::default(),
            error_handler: Default::default(),
            debug,
        }
    }
    // we have to consider the following cases:
    // 1. declaration before definition
    // 2. 2nd declaration before definition
    // 3. definition
    // 4. declaration after definition

    // 1. should declare `id` a import unless specified as `static`.
    // 3. should always declare `id` as export or local.
    // 2. and 4. should be a no-op.
    fn declare_func(&mut self, symbol: Symbol, is_definition: bool) -> CompileResult<FuncId> {
        use saltwater_parser::get_str;
        if !is_definition {
            // case 2 and 4
            if let Some(Id::Function(func_id)) = self.declarations.get(&symbol) {
                return Ok(*func_id);
            }
        }
        let metadata = symbol.get();
        let func_type = match &metadata.ctype {
            Type::Function(func_type) => func_type,
            _ => unreachable!("bug in backend: only functions should be passed to `declare_func`"),
        };
        let signature = func_type.signature(self.module.isa());
        let linkage = match metadata.storage_class {
            StorageClass::Auto | StorageClass::Extern if is_definition => Linkage::Export,
            StorageClass::Auto | StorageClass::Extern => Linkage::Import,
            StorageClass::Static => Linkage::Local,
            StorageClass::Register | StorageClass::Typedef => unreachable!(),
        };
        let func_id = self
            .module
            .declare_function(get_str!(metadata.id), linkage, &signature)
            .unwrap_or_else(|err| panic!("{}", err));
        self.declarations.insert(symbol, Id::Function(func_id));
        Ok(func_id)
    }
    /// declare an object on the stack
    fn declare_stack(
        &mut self,
        decl: Declaration,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> CompileResult<()> {
        let meta = decl.symbol.get();
        if let StorageClass::Typedef = meta.storage_class {
            return Ok(());
        }
        if let Type::Function(_) = &meta.ctype {
            self.declare_func(decl.symbol, false)?;
            return Ok(());
        }
        let u64_size = match meta.ctype.sizeof() {
            Ok(size) => size,
            Err(err) => {
                return Err(CompileError::semantic(Locatable {
                    data: err.into(),
                    location,
                }))
            }
        };
        let kind = StackSlotKind::ExplicitSlot;
        let size = match u32::try_from(u64_size) {
            Ok(size) => size,
            Err(_) => return Err(CompileError::semantic(Locatable {
                data: "cannot store items on the stack that are more than 4 GB, it will overflow the stack".into(),
                location,
            }))
        };
        let data = StackSlotData {
            kind,
            size,
            offset: None,
        };
        let stack_slot = builder.create_stack_slot(data);
        self.declarations.insert(decl.symbol, Id::Local(stack_slot));
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
    ) -> CompileResult<()> {
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
        params: &[Symbol],
        func_start: Block,
        location: &Location,
        builder: &mut FunctionBuilder,
    ) -> CompileResult<()> {
        // Cranelift requires that all block params are declared up front
        let ir_vals: Vec<_> = params
            .iter()
            .map(|param| {
                let ir_type = param.get().ctype.as_ir_type();
                Ok(builder.append_block_param(func_start, ir_type))
            })
            .collect::<CompileResult<_>>()?;
        for (&param, ir_val) in params.iter().zip(ir_vals) {
            let u64_size = match param.get().ctype.sizeof() {
                Err(data) => semantic_err!(data.into(), *location),
                Ok(size) => size,
            };
            let u32_size = match u32::try_from(u64_size) {
                Err(_) => semantic_err!(
                    format!(
                        "size {} is too large for stack (can only handle 32-bit values)",
                        u64_size
                    ),
                    *location
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
            self.declarations.insert(param, Id::Local(slot));
        }
        Ok(())
    }
    fn compile_func(
        &mut self,
        symbol: Symbol,
        func_type: &FunctionType,
        stmts: Vec<Stmt>,
        location: Location,
    ) -> CompileResult<()> {
        let func_id = self.declare_func(symbol, true)?;
        // TODO: make declare_func should take a `signature` after all?
        // This just calculates it twice, it's probably fine
        let signature = func_type.signature(self.module.isa());

        // external name is meant to be a lookup in a symbol table,
        // but we just give it garbage values
        let mut func = Function::with_name_signature(ExternalName::user(0, 0), signature);

        // this context is just boiler plate
        let mut ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut ctx);

        let func_start = builder.create_block();
        builder.switch_to_block(func_start);

        let should_ret = func_type.should_return();
        if func_type.has_params() {
            self.store_stack_params(
                // TODO: get rid of this clone
                &func_type.params,
                func_start,
                &location,
                &mut builder,
            )?;
        }
        self.compile_all(stmts, &mut builder)?;
        if !builder.is_filled() {
            let id = symbol.get().id;
            if id == InternedStr::get_or_intern("main") {
                let ir_int = func_type.return_type.as_ir_type();
                let zero = [builder.ins().iconst(ir_int, 0)];
                builder.ins().return_(&zero);
            } else if should_ret {
                semantic_err!(
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
        builder.seal_all_blocks();
        builder.finalize();

        let flags = settings::Flags::new(settings::builder());

        if self.debug {
            println!("ir: {}", func);
        }

        if let Err(err) = codegen::verify_function(&func, &flags) {
            panic!(
                "verification error: {}\nnote: while compiling {}",
                err, func
            );
        }

        let mut ctx = codegen::Context::for_function(func);
        let mut trap_sink = codegen::binemit::NullTrapSink {};
        if let Err(err) = self
            .module
            .define_function(func_id, &mut ctx, &mut trap_sink)
        {
            panic!(
                "definition error: {}\nnote: while compiling {}",
                err, ctx.func
            );
        }

        Ok(())
    }
}

pub type Product = <cranelift_object::ObjectBackend as Backend>::Product;

/// Compiles a single declaration.
pub fn compile_decl<B: Backend>(
    module: Module<B>,
    decl: Locatable<Declaration>,
    debug_asm: bool,
) -> Result<Module<B>, CompileError> {
    let mut compiler = Compiler::new(module, debug_asm);
    let mut err = None;

    let meta = decl.data.symbol.get();

    if !matches!(meta.storage_class, StorageClass::Typedef) {
        let current = match &meta.ctype {
            Type::Function(func_type) => match decl.data.init {
                Some(Initializer::FunctionBody(stmts)) => {
                    compiler.compile_func(decl.data.symbol, &func_type, stmts, decl.location)
                }
                None => compiler.declare_func(decl.data.symbol, false).map(|_| ()),
                _ => unreachable!("functions can only be initialized by a FunctionBody"),
            },
            Type::Void | Type::Error => unreachable!("parser let an incomplete type through"),
            _ => {
                if let Some(Initializer::FunctionBody(_)) = &decl.data.init {
                    unreachable!("only functions should have a function body")
                }
                compiler.store_static(decl.data.symbol, decl.data.init, decl.location)
            }
        };
        err = current.err();
    }

    if let Some(err) = err {
        Err(err)
    } else {
        Ok(compiler.module)
    }
}

/// Compile and return the declarations and warnings.
pub fn compile<B: Backend>(module: Module<B>, buf: &str, opt: Opt) -> Program<Module<B>> {
    use saltwater_parser::{check_semantics, vec_deque};

    let debug_asm = opt.debug_asm;
    let mut program = check_semantics(buf, opt);
    let hir = match program.result {
        Ok(hir) => hir,
        Err(err) => {
            return Program {
                result: Err(err),
                warnings: program.warnings,
                files: program.files,
            }
        }
    };
    // really we'd like to have all errors but that requires a refactor
    let mut err = None;
    let mut compiler = Compiler::new(module, debug_asm);
    for decl in hir {
        let meta = decl.data.symbol.get();
        if let StorageClass::Typedef = meta.storage_class {
            continue;
        }
        let current = match &meta.ctype {
            Type::Function(func_type) => match decl.data.init {
                Some(Initializer::FunctionBody(stmts)) => {
                    compiler.compile_func(decl.data.symbol, &func_type, stmts, decl.location)
                }
                None => compiler.declare_func(decl.data.symbol, false).map(|_| ()),
                _ => unreachable!("functions can only be initialized by a FunctionBody"),
            },
            Type::Void | Type::Error => unreachable!("parser let an incomplete type through"),
            _ => {
                if let Some(Initializer::FunctionBody(_)) = &decl.data.init {
                    unreachable!("only functions should have a function body")
                }
                compiler.store_static(decl.data.symbol, decl.data.init, decl.location)
            }
        };
        if let Err(e) = current {
            err = Some(e);
            break;
        }
    }
    let warns = compiler.error_handler.warnings;
    let (result, ir_warnings) = if let Some(err) = err {
        (Err(err), warns)
    } else {
        (Ok(compiler.module), warns)
    };
    program.warnings.extend(ir_warnings);
    Program {
        result: result.map_err(|errs| vec_deque![errs]),
        warnings: program.warnings,
        files: program.files,
    }
}

pub fn assemble(product: Product, output: &Path) -> Result<(), saltwater_parser::Error> {
    use std::fs::File;
    use std::io::{self, Write};

    let bytes = product.emit().map_err(saltwater_parser::Error::Platform)?;
    File::create(output)?
        .write_all(&bytes)
        .map_err(io::Error::into)
}

pub fn link(obj_file: &Path, output: &Path) -> Result<(), std::io::Error> {
    use std::io::{Error, ErrorKind};
    use std::process::Command;

    // link the .o file using host linker
    let status = Command::new("cc")
        .args(&[&obj_file, Path::new("-o"), output])
        .status()
        .map_err(|err| {
            if err.kind() == ErrorKind::NotFound {
                Error::new(
                    ErrorKind::NotFound,
                    "could not find host cc (for linking). Is it on your PATH?",
                )
            } else {
                err
            }
        })?;
    if !status.success() {
        Err(Error::new(ErrorKind::Other, "linking program failed"))
    } else {
        Ok(())
    }
}

#[cfg(feature = "jit")]
pub use jit::*;

#[cfg(feature = "jit")]
mod jit {
    use super::*;
    use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};
    use std::convert::TryFrom;
    use std::rc::Rc;

    pub fn initialize_jit_module() -> Module<SimpleJITBackend> {
        let libcall_names = cranelift_module::default_libcall_names();
        Module::new(SimpleJITBuilder::with_isa(get_isa(true), libcall_names))
    }

    /// Structure used to handle compiling C code to memory instead of to disk.
    ///
    /// You can use [`from_string`] to create a JIT instance.
    /// Alternatively, if you don't care about compile warnings, you can use `JIT::try_from` instead.
    /// If you already have a `Module`, you can use `JIT::from` to avoid having to `unwrap()`.
    ///
    /// JIT stands for 'Just In Time' compiled, the way that Java and JavaScript work.
    ///
    /// [`from_string`]: #method.from_string
    pub struct JIT {
        module: Module<SimpleJITBackend>,
    }

    impl From<Module<SimpleJITBackend>> for JIT {
        fn from(module: Module<SimpleJITBackend>) -> Self {
            Self { module }
        }
    }

    impl TryFrom<Rc<str>> for JIT {
        type Error = saltwater_parser::Error;
        fn try_from(source: Rc<str>) -> Result<JIT, Self::Error> {
            JIT::from_string(source, Opt::default()).result
        }
    }

    impl JIT {
        /// Compile string and return JITed code.
        pub fn from_string<R: Into<Rc<str>>>(
            source: R,
            opt: Opt,
        ) -> Program<Self, saltwater_parser::Error> {
            let source = source.into();
            let module = initialize_jit_module();
            let program = compile(module, &source, opt);
            let result = match program.result {
                Ok(module) => Ok(JIT::from(module)),
                Err(errs) => Err(errs.into()),
            };
            Program {
                result,
                warnings: program.warnings,
                files: program.files,
            }
        }

        /// Invoke this function before trying to get access to "new" compiled functions.
        pub fn finalize(&mut self) {
            self.module.finalize_definitions();
        }
        /// Get a compiled function. If this function doesn't exist then `None` is returned, otherwise its address returned.
        ///
        /// # Panics
        /// Panics if function is not compiled (finalized). Try to invoke `finalize` before using `get_compiled_function`.
        pub fn get_compiled_function(&mut self, name: &str) -> Option<*const u8> {
            use cranelift_module::FuncOrDataId;

            let name = self.module.get_name(name);
            if let Some(FuncOrDataId::Func(id)) = name {
                Some(self.module.get_finalized_function(id))
            } else {
                None
            }
        }
        /// Get compiled static data. If this data doesn't exist then `None` is returned, otherwise its address and size are returned.
        pub fn get_compiled_data(&mut self, name: &str) -> Option<(*mut u8, usize)> {
            use cranelift_module::FuncOrDataId;

            let name = self.module.get_name(name);
            if let Some(FuncOrDataId::Data(id)) = name {
                Some(self.module.get_finalized_data(id))
            } else {
                None
            }
        }
        /// Given a module, run the `main` function.
        ///
        /// This automatically calls `self.finalize()`.
        /// If `main()` does not exist in the module, returns `None`; otherwise returns the exit code.
        ///
        /// # Safety
        /// This function runs arbitrary C code.
        /// It can segfault, access out-of-bounds memory, cause data races, or do anything else C can do.
        #[allow(unsafe_code)]
        pub unsafe fn run_main(&mut self) -> Option<i32> {
            self.finalize();
            let main = self.get_compiled_function("main")?;
            let args = std::env::args().skip(1);
            let argc = args.len() as i32;
            // CString should be alive if we want to pass its pointer to another function,
            // otherwise this may lead to UB.
            let vec_args = args
                .map(|string| std::ffi::CString::new(string).unwrap())
                .collect::<Vec<_>>();
            // This vec needs to be stored so we aren't passing a pointer to a freed temporary.
            let argv = vec_args
                .iter()
                .map(|cstr| cstr.as_ptr() as *const u8)
                .collect::<Vec<_>>();
            assert_ne!(main, std::ptr::null());
            // this transmute is safe: this function is finalized (`self.finalize()`)
            // and **guaranteed** to be non-null
            let main: unsafe extern "C" fn(i32, *const *const u8) -> i32 =
                std::mem::transmute(main);
            // though transmute is safe, invoking this function is unsafe because we invoke C code.
            Some(main(argc, argv.as_ptr() as *const *const u8))
        }
    }
}

#[cfg(test)]
#[test]
fn test_compile_error_semantic() {
    assert_eq!(
        CompileError::semantic(Location::default().with("".to_string())).data,
        Error::Semantic(SemanticError::Generic("".to_string())),
    );
}
