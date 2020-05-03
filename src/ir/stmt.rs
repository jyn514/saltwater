use cranelift::codegen::cursor::Cursor;
use cranelift::codegen::ir::entities::Inst;
use cranelift::frontend::Switch;
use cranelift::prelude::{Block, FunctionBuilder, InstBuilder};
use cranelift_module::Backend;

use super::Compiler;
use crate::data::{
    hir::{Expr, Stmt, StmtType},
    *,
};

impl<B: Backend> Compiler<B> {
    pub(super) fn compile_all(
        &mut self,
        stmts: Vec<Stmt>,
        builder: &mut FunctionBuilder,
    ) -> CompileResult<()> {
        for stmt in stmts {
            self.compile_stmt(stmt, builder)?;
        }
        Ok(())
    }
    pub(super) fn compile_stmt(
        &mut self,
        stmt: Stmt,
        builder: &mut FunctionBuilder,
    ) -> CompileResult<()> {
        if builder.is_filled() && !stmt.data.is_jump_target() {
            return Err(stmt.location.error(SemanticError::UnreachableStatement));
        }
        match stmt.data {
            StmtType::Compound(stmts) => self.compile_all(stmts, builder),
            // INVARIANT: symbol has not yet been declared in this scope
            StmtType::Decl(decls) => {
                for decl in decls {
                    self.declare_stack(decl.data, decl.location, builder)?;
                }
                Ok(())
            }
            StmtType::Expr(expr) => {
                self.compile_expr(expr, builder)?;
                Ok(())
            }
            StmtType::Return(expr) => {
                let mut ret = vec![];
                let pretty = expr.as_ref().map_or("void".into(), |e| e.to_string());
                if let Some(e) = expr {
                    let val = self.compile_expr(e, builder)?;
                    ret.push(val.ir_val);
                }
                let inst = builder.ins().return_(&ret);
                self.add_comment(inst, format!("return {}", pretty));
                Ok(())
            }
            StmtType::If(condition, body, otherwise) => {
                self.if_stmt(condition, *body, otherwise, builder)
            }
            StmtType::While(condition, body) => self.while_stmt(Some(condition), *body, builder),
            StmtType::Break | StmtType::Continue => {
                self.loop_exit(stmt.data == StmtType::Break, stmt.location, builder)
            }
            StmtType::For(init, condition, post_loop, body) => self.for_loop(
                *init,
                condition.map(|e| *e),
                post_loop.map(|e| *e),
                *body,
                stmt.location,
                builder,
            ),
            StmtType::Do(body, condition) => self.do_loop(*body, condition, builder),
            StmtType::Switch(condition, body) => self.switch(condition, *body, builder),
            StmtType::Label(name, inner) => {
                let new_block = builder.create_block();
                if let Some(jump) = Self::jump_to_block(new_block, builder) {
                    self.add_comment(jump, format!("{}:", name));
                }
                builder.switch_to_block(new_block);
                if let Some(previous) = self.labels.insert(name, new_block) {
                    Err(stmt
                        .location
                        .error(SemanticError::LabelRedeclaration(previous)))
                } else {
                    self.compile_stmt(*inner, builder)
                }
            }
            StmtType::Goto(name) => match self.labels.get(&name) {
                Some(block) => {
                    Self::jump_to_block(*block, builder);
                    Ok(())
                }
                None => Err(stmt.location.error(SemanticError::UndeclaredLabel(name))),
            },
            StmtType::Case(constexpr, inner) => {
                self.case(constexpr, *inner, stmt.location, builder)
            }
            StmtType::Default(inner) => self.default(*inner, stmt.location, builder),
        }
    }
    fn if_stmt(
        &mut self,
        condition: Expr,
        body: Stmt,
        otherwise: Option<Box<Stmt>>,
        builder: &mut FunctionBuilder,
    ) -> CompileResult<()> {
        // If condtion is zero:
        //      If else_block exists, jump to else_block + compile_all
        //      Otherwise, jump to end_block
        //  Otherwise:
        //      Fallthrough to if_body + compile_all
        //      If else_block exists, jump to end_block + compile_all
        //      Otherwise, fallthrough to end_block
        let condition = self.compile_expr(condition, builder)?;
        let (if_body, end_body) = (builder.create_block(), builder.create_block());
        if let Some(other) = otherwise {
            let else_body = builder.create_block();
            builder.ins().brz(condition.ir_val, else_body, &[]);
            builder.ins().jump(if_body, &[]);

            builder.switch_to_block(if_body);
            self.compile_stmt(body, builder)?;
            let if_has_return = builder.is_filled();
            Self::jump_to_block(end_body, builder);

            builder.switch_to_block(else_body);
            self.compile_stmt(*other, builder)?;
            if !builder.is_filled() {
                builder.ins().jump(end_body, &[]);
                builder.switch_to_block(end_body);
            // if we returned in both 'if' and 'else' blocks, all following code is unreachable
            // this is the case where we returned in 'else' but not 'if'
            } else if !if_has_return {
                builder.switch_to_block(end_body);
            }
        } else {
            builder.ins().brz(condition.ir_val, end_body, &[]);
            builder.ins().jump(if_body, &[]);

            builder.switch_to_block(if_body);
            self.compile_stmt(body, builder)?;
            Self::jump_to_block(end_body, builder);

            builder.switch_to_block(end_body);
        };
        Ok(())
    }
    /// Enter a loop context:
    /// - Create a new start and end block
    /// - Switch to the start block
    /// - Return (start, end, previous_last_saw_loop)
    fn enter_loop(&mut self, builder: &mut FunctionBuilder) -> (Block, Block, bool) {
        let (loop_body, end_body) = (builder.create_block(), builder.create_block());
        self.loops.push((loop_body, end_body));
        let old_saw_loop = self.last_saw_loop;
        self.last_saw_loop = true;

        builder.ins().jump(loop_body, &[]);
        builder.switch_to_block(loop_body);
        (loop_body, end_body, old_saw_loop)
    }
    /// Exit a loop
    fn exit_loop(&mut self, old_saw_loop: bool) {
        self.loops.pop();
        self.last_saw_loop = old_saw_loop;
    }
    fn while_stmt(
        &mut self,
        maybe_condition: Option<Expr>,
        body: Stmt,
        builder: &mut FunctionBuilder,
    ) -> CompileResult<()> {
        let (loop_body, end_body, old_saw_loop) = self.enter_loop(builder);

        // for loops can loop forever: `for (;;) {}`
        if let Some(condition) = maybe_condition {
            let pretty = format!("while ({})", condition);
            let condition = self.compile_expr(condition, builder)?;
            let inst = builder.ins().brz(condition.ir_val, end_body, &[]);
            self.add_comment(inst, pretty);
            self.fallthrough(builder);
        }

        self.compile_stmt(body, builder)?;
        Self::jump_to_block(loop_body, builder);

        builder.switch_to_block(end_body);
        self.exit_loop(old_saw_loop);
        Ok(())
    }
    pub(super) fn fallthrough(&self, builder: &mut FunctionBuilder) {
        let bb = builder.create_block();
        builder.ins().jump(bb, &[]);
        builder.switch_to_block(bb);
    }
    fn do_loop(
        &mut self,
        body: Stmt,
        condition: Expr,
        builder: &mut FunctionBuilder,
    ) -> CompileResult<()> {
        let (loop_body, end_body, old_saw_loop) = self.enter_loop(builder);

        self.compile_stmt(body, builder)?;
        if builder.is_filled() {
            return Err(condition
                .location
                .error(SemanticError::UnreachableStatement));
        }
        let condition = self.compile_expr(condition, builder)?;
        builder.ins().brz(condition.ir_val, end_body, &[]);
        Self::jump_to_block(loop_body, builder);

        builder.switch_to_block(end_body);
        self.exit_loop(old_saw_loop);
        Ok(())
    }
    fn for_loop(
        &mut self,
        init: Stmt,
        condition: Option<Expr>,
        post_loop: Option<Expr>,
        mut body: Stmt,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> CompileResult<()> {
        self.compile_stmt(init, builder)?;
        if let Some(post_loop) = post_loop {
            let post_loop = Stmt {
                data: StmtType::Expr(post_loop),
                location,
            };
            if let Stmt {
                data: StmtType::Compound(stmts),
                ..
            } = &mut body
            {
                stmts.push(post_loop);
            } else {
                body = Stmt {
                    data: StmtType::Compound(vec![body, post_loop]),
                    location,
                };
            };
        }
        self.while_stmt(condition, body, builder)
    }
    fn switch(
        &mut self,
        condition: Expr,
        body: Stmt,
        builder: &mut FunctionBuilder,
    ) -> CompileResult<()> {
        let cond_val = self.compile_expr(condition, builder)?;
        // works around https://github.com/CraneStation/cranelift/issues/1057
        // instead of switching to back to the current block to emit the Switch,
        // fill a new dummy block
        let dummy_block = builder.create_block();
        Self::jump_to_block(dummy_block, builder);

        let start_block = builder.create_block();
        builder.switch_to_block(start_block);
        let old_saw_loop = self.last_saw_loop;
        self.last_saw_loop = false;

        self.switches
            .push((Switch::new(), None, builder.create_block()));
        self.compile_stmt(body, builder)?;
        let (switch, default, end) = self.switches.pop().unwrap();
        self.last_saw_loop = old_saw_loop;

        Self::jump_to_block(end, builder);
        builder.switch_to_block(dummy_block);
        switch.emit(
            builder,
            cond_val.ir_val,
            if let Some(default) = default {
                default
            } else {
                end
            },
        );
        builder.switch_to_block(end);
        Ok(())
    }
    fn case(
        &mut self,
        constexpr: u64,
        stmt: Stmt,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> CompileResult<()> {
        let (switch, _, _) = match self.switches.last_mut() {
            Some(x) => x,
            None => {
                return Err(location.error(SemanticError::CaseOutsideSwitch { is_default: false }))
            }
        };
        if switch.entries().contains_key(&constexpr) {
            return Err(location.error(SemanticError::DuplicateCase { is_default: false }));
        }
        if builder.is_pristine() {
            let current = builder.cursor().current_block().unwrap();
            switch.set_entry(constexpr, current);
            self.add_comment(current, format!("case {}", constexpr));
        } else {
            let new = builder.create_block();
            switch.set_entry(constexpr, new);
            Self::jump_to_block(new, builder);
            builder.switch_to_block(new);
            self.add_comment(new, format!("case {}", constexpr));
        };
        self.compile_stmt(stmt, builder)
    }
    fn default(
        &mut self,
        inner: Stmt,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> CompileResult<()> {
        let (_, default, _) = match self.switches.last_mut() {
            Some(x) => x,
            None => {
                return Err(location.error(SemanticError::CaseOutsideSwitch { is_default: true }));
            }
        };
        if default.is_some() {
            Err(location.error(SemanticError::DuplicateCase { is_default: true }))
        } else {
            let default_block = if builder.is_pristine() {
                builder.cursor().current_block().unwrap()
            } else {
                let new = builder.create_block();
                Self::jump_to_block(new, builder);
                builder.switch_to_block(new);
                new
            };
            *default = Some(default_block);
            self.add_comment(default_block, "default:");
            self.compile_stmt(inner, builder)
        }
    }
    fn loop_exit(
        &mut self,
        is_break: bool,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> CompileResult<()> {
        if self.last_saw_loop {
            // break from loop
            if let Some((loop_start, loop_end)) = self.loops.last() {
                if is_break {
                    Self::jump_to_block(*loop_end, builder);
                } else {
                    Self::jump_to_block(*loop_start, builder);
                }
                Ok(())
            } else {
                semantic_err!(
                    format!(
                        "'{}' statement not in loop or switch statement",
                        if is_break { "break" } else { "continue" }
                    ),
                    location
                );
            }
        } else if !is_break {
            semantic_err!("'continue' not in loop".into(), location);
        } else {
            // break from switch
            let (_, _, end_block) = self
                .switches
                .last()
                .expect("should be in a switch if last_saw_loop is false");
            let inst = builder.ins().jump(*end_block, &[]);
            self.add_comment(inst, "break from switch");
            Ok(())
        }
    }
    #[inline]
    fn jump_to_block(block: Block, builder: &mut FunctionBuilder) -> Option<Inst> {
        if !builder.is_filled() {
            Some(builder.ins().jump(block, &[]))
        } else {
            None
        }
    }
}

impl StmtType {
    fn is_jump_target(&self) -> bool {
        match self {
            StmtType::Case(_, _) | StmtType::Default(_) | StmtType::Label(_, _) => true,
            _ => false,
        }
    }
}
