use crate::data::{
    Declaration, Expr, FunctionType, Initializer, Locatable, Mir, Reg, Stmt, Symbol, Type,
};

pub struct MirCompiler {
    static_init: i64,
    addr: i64,
    reg: i64,
    label: i64,
    mir: Vec<Mir>,
}

impl Iterator for MirCompiler {
    type Item = Result<Stmt, Locatable<String>>;
    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

pub fn compile(program: Vec<Declaration>) -> Vec<Mir> {
    let mut compiler = MirCompiler::new();
    for decl in program {
        if let Some(init) = decl.init {
            match &decl.symbol.ctype {
                Type::Void => panic!("parser let an incomplete type through"),
                Type::Function(func_type) => compiler.compile_func(func_type.clone(), init),
                x => compiler.store_static(decl.symbol, init),
            }
        }
    }
    compiler.mir
}

impl MirCompiler {
    fn new() -> MirCompiler {
        MirCompiler {
            static_init: 0,
            addr: 0,
            reg: 0,
            label: 0,
            mir: vec![],
        }
    }
    fn compile_func(&mut self, func: FunctionType, init: Initializer) {
        let stmts = match init {
            Initializer::CompoundStatement(stmts) => stmts,
            x => panic!("expected compound statement from parser, got '{:#?}'", x),
        };
        self.compile_all(stmts)
    }
    fn compile_all(&mut self, stmts: Vec<Stmt>) {
        for stmt in stmts {
            self.compile_stmt(stmt);
        }
    }
    fn compile_stmt(&mut self, stmt: Stmt) {
        match stmt {
            Stmt::Compound(stmts) => self.compile_all(stmts),
            Stmt::If(condition, body, otherwise) => {
                let jmp_if_false = self.label;
                self.label += 1;
                let reg = self.compile_expr(condition);
            }
            _ => unimplemented!("almost every statement"),
        }
    }
    fn compile_expr(&mut self, expr: Expr) -> Reg {
        0
    }
    fn store_static(&mut self, symbol: Symbol, init: Initializer) {
        let mir = Mir::StaticInit(self.addr, init);
        self.addr += 1;
        self.mir.push(mir);
    }
}
