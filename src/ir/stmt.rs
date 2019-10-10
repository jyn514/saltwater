use cranelift::codegen::cursor::Cursor;
use cranelift::frontend::Switch;
use cranelift::prelude::{Ebb, FunctionBuilder, InstBuilder};

use super::Compiler;
use crate::data::prelude::*;

impl Compiler {
    pub(crate) fn compile_all(
        &mut self,
        stmts: Vec<Stmt>,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        for stmt in stmts {
            self.compile_stmt(stmt, builder)?;
        }
        Ok(())
    }
    pub(crate) fn compile_stmt(
        &mut self,
        stmt: Stmt,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        if builder.is_filled() && !stmt.data.is_jump_target() {
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
                if let Some(e) = expr {
                    let val = self.compile_expr(e, builder)?;
                    ret.push(val.ir_val);
                }
                builder.ins().return_(&ret);
                Ok(())
            }
            StmtType::If(condition, body, otherwise) => {
                self.if_stmt(condition, *body, otherwise, builder)
            }
            StmtType::While(condition, maybe_body) => {
                self.while_stmt(Some(condition), maybe_body.map(|b| *b), builder)
            }
            StmtType::Break | StmtType::Continue => {
                self.loop_exit(stmt.data == StmtType::Break, stmt.location, builder)
            }
            StmtType::For(init, condition, post_loop, body) => {
                self.for_loop(init, condition, post_loop, body, stmt.location, builder)
            }
            StmtType::Do(body, condition) => self.do_loop(*body, condition, builder),
            StmtType::Switch(condition, body) => self.switch(condition, *body, builder),
            StmtType::Label(_) | StmtType::Goto(_) => unimplemented!("codegen goto"),
            StmtType::Case(constexpr, inner) => self.case(constexpr, inner, stmt.location, builder),
            StmtType::Default(inner) => self.default(inner, stmt.location, builder),
        }
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

            builder.switch_to_block(if_body);
            self.compile_stmt(body, builder)?;
            Self::jump_to_block(end_body, builder);
            let if_has_return = builder.is_filled();

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
    /// - Create a new start and end EBB
    /// - Switch to the start EBB
    /// - Return (start, end, previous_last_saw_loop)
    fn enter_loop(&mut self, builder: &mut FunctionBuilder) -> (Ebb, Ebb, bool) {
        let (loop_body, end_body) = (builder.create_ebb(), builder.create_ebb());
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
        maybe_body: Option<Stmt>,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        let (loop_body, end_body, old_saw_loop) = self.enter_loop(builder);

        // for loops can loop forever: `for (;;) {}`
        if let Some(condition) = maybe_condition {
            let condition = self.compile_expr(condition, builder)?;
            builder.ins().brz(condition.ir_val, end_body, &[]);
        }

        if let Some(body) = maybe_body {
            self.compile_stmt(body, builder)?;
        }
        Self::jump_to_block(loop_body, builder);

        builder.switch_to_block(end_body);
        self.exit_loop(old_saw_loop);
        Ok(())
    }
    fn do_loop(
        &mut self,
        body: Stmt,
        condition: Expr,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        let (loop_body, end_body, old_saw_loop) = self.enter_loop(builder);

        self.compile_stmt(body, builder)?;
        let condition = self.compile_expr(condition, builder)?;
        builder.ins().brz(condition.ir_val, end_body, &[]);
        Self::jump_to_block(loop_body, builder);

        builder.switch_to_block(end_body);
        self.exit_loop(old_saw_loop);
        Ok(())
    }
    fn for_loop(
        &mut self,
        init: Option<Box<Stmt>>,
        condition: Option<Expr>,
        post_loop: Option<Expr>,
        body: Option<Box<Stmt>>,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        if let Some(init) = init {
            self.compile_stmt(*init, builder)?;
        }
        let mut body = body.map(|x| *x);
        if let Some(post_loop) = post_loop {
            let post_loop = Stmt {
                data: StmtType::Expr(post_loop),
                location: location.clone(),
            };
            if let Some(Stmt {
                data: StmtType::Compound(stmts),
                ..
            }) = &mut body
            {
                stmts.push(post_loop);
            } else if let Some(other) = body {
                body = Some(Stmt {
                    data: StmtType::Compound(vec![other, post_loop]),
                    location,
                });
            } else {
                body = Some(post_loop);
            };
        }
        self.while_stmt(condition, body, builder)
    }
    fn switch(
        &mut self,
        condition: Expr,
        body: Stmt,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        let cond_val = self.compile_expr(condition, builder)?;
        // works around https://github.com/CraneStation/cranelift/issues/1057
        // instead of switching to back to the current block to emit the Switch,
        // fill a new dummy block
        let dummy_block = builder.create_ebb();
        Self::jump_to_block(dummy_block, builder);

        let start_block = builder.create_ebb();
        builder.switch_to_block(start_block);
        self.last_saw_loop = false;

        self.switches
            .push((Switch::new(), None, builder.create_ebb()));
        self.compile_stmt(body, builder)?;
        let (switch, default, end) = self.switches.pop().unwrap();

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
        stmt: Option<Box<Stmt>>,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        let (switch, _, _) = match self.switches.last_mut() {
            Some(x) => x,
            None => {
                return Err(Locatable {
                    data: "case outside of switch statement".into(),
                    location,
                })
            }
        };
        if builder.is_pristine() {
            let current = builder.cursor().current_ebb().unwrap();
            switch.set_entry(constexpr, current);
        } else {
            let new = builder.create_ebb();
            switch.set_entry(constexpr, new);
            Self::jump_to_block(new, builder);
            builder.switch_to_block(new);
        };
        if let Some(stmt) = stmt {
            self.compile_stmt(*stmt, builder)
        } else {
            Ok(())
        }
    }
    fn default(
        &mut self,
        inner: Option<Box<Stmt>>,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
        let (_, default, _) = match self.switches.last_mut() {
            Some(x) => x,
            None => {
                return Err(Locatable {
                    data: "default case outside of switch statement".into(),
                    location,
                })
            }
        };
        if default.is_some() {
            Err(Locatable {
                data: "cannot have multiple default cases in a switch statement".into(),
                location,
            })
        } else {
            let default_ebb = if builder.is_pristine() {
                builder.cursor().current_ebb().unwrap()
            } else {
                let new = builder.create_ebb();
                Self::jump_to_block(new, builder);
                builder.switch_to_block(new);
                new
            };
            *default = Some(default_ebb);
            if let Some(stmt) = inner {
                self.compile_stmt(*stmt, builder)
            } else {
                Ok(())
            }
        }
    }
    fn loop_exit(
        &mut self,
        is_break: bool,
        location: Location,
        builder: &mut FunctionBuilder,
    ) -> SemanticResult<()> {
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
                err!(
                    format!(
                        "'{}' statement not in loop or switch statement",
                        if is_break { "break" } else { "continue" }
                    ),
                    location
                );
            }
        } else if !is_break {
            err!("'continue' not in loop".into(), location);
        } else {
            // break from switch
            let (_, _, end_block) = self
                .switches
                .last()
                .expect("should be in a switch if last_saw_loop is false");
            builder.ins().jump(*end_block, &[]);
            Ok(())
        }
    }
    #[inline]
    fn jump_to_block(ebb: Ebb, builder: &mut FunctionBuilder) {
        if !builder.is_filled() {
            builder.ins().jump(ebb, &[]);
        }
    }
}

impl StmtType {
    fn is_jump_target(&self) -> bool {
        match self {
            StmtType::Case(_, _) | StmtType::Default(_) | StmtType::Label(_) => true,
            _ => false,
        }
    }
}
