use super::{Lexeme, Parser};
use crate::data::*;
use crate::utils::{error, warn};

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    /// Original:
    /// expr:
    ///      assignment_expr
    ///      | expr ',' assignment_expr
    ///      ;
    ///
    /// We rewrite it as follows:
    /// expr:
    ///     assignment_expr (',' assignment_expr)*
    ///     ;
    pub fn expr(&mut self) -> Result<Stmt, Locatable<String>> {
        Ok(Stmt::Expr(Expr::Id(self.next_token().unwrap().data)))
    }

    /// assignment_expr
    /// : conditional_expr
    /// | unary_expr assignment_operator assignment_expr
    /// ;
    ///
    /// NOTE: although the grammar shows any unary_expr on the left hand of assignment,
    /// only '*' cast_expr has been found to be valid. Tested with clang.
    fn assignment_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// conditional_expr
    /// : logical_or_expr
    /// | logical_or_expr '?' expr ':' conditional_expr
    /// ;
    fn conditional_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// Original:
    /// logical_or_expr
    /// : logical_and_expr
    /// | logical_or_expr OR_OP logical_and_expr
    /// ;
    ///
    /// Rewritten:
    /// logical_or_expr:
    ///     logical_and_expr (OR_OP logical_and_expr)*
    fn logical_or_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// logical_and_expr
    /// : inclusive_or_expr
    /// | logical_and_expr AND_OP inclusive_or_expr
    /// ;
    ///
    /// Rewritten similar to logical_or_expr above.
    fn logical_and_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// inclusive_or_expr
    /// : exclusive_or_expr
    /// | inclusive_or_expr '|' exclusive_or_expr
    /// ;
    ///
    /// Rewritten similarly.
    fn inclusive_or_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// exclusive_or_expr
    /// : and_expr
    /// | exclusive_or_expr '^' and_expr
    /// ;
    fn exclusive_or_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// and_expr
    /// : equality_expr
    /// | and_expr '&' equality_expr
    /// ;
    fn and_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// equality_expr
    /// : relational_expr
    /// | equality_expr EQ_OP relational_expr
    /// | equality_expr NE_OP relational_expr
    /// ;
    fn equality_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// relational_expr
    /// : shift_expr
    /// | relational_expr '<' shift_expr
    /// | relational_expr '>' shift_expr
    /// | relational_expr LE_OP shift_expr
    /// | relational_expr GE_OP shift_expr
    /// ;
    fn relational_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// shift_expr
    /// : additive_expr
    /// | shift_expr LEFT_OP additive_expr
    /// | shift_expr RIGHT_OP additive_expr
    /// ;
    fn shift_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// additive_expr
    /// : multiplicative_expr
    /// | additive_expr '+' multiplicative_expr
    /// | additive_expr '-' multiplicative_expr
    /// ;
    fn additive_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// multiplicative_expr
    /// : cast_expr
    /// | multiplicative_expr '*' cast_expr
    /// | multiplicative_expr '/' cast_expr
    /// | multiplicative_expr '%' cast_expr
    /// ;
    fn multiplicative_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// cast_expr
    /// : unary_expr
    /// | '(' type_name ')' cast_expr
    /// ;
    ///
    /// TODO: type_name should be in decl.rs, not here
    fn cast_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// unary_expr
    /// : postfix_expr
    /// | INC_OP unary_expr
    /// | DEC_OP unary_expr
    /// | unary_operator cast_expr
    /// | SIZEOF unary_expr
    /// | SIZEOF '(' type_name ')'
    /// ;
    fn unary_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// postfix_expr
    /// : primary_expr
    /// | postfix_expr '[' expr ']'
    /// | postfix_expr '(' argument_expr_list_opt ')'
    /// | postfix_expr '.' identifier
    /// | postfix_expr PTR_OP identifier
    /// | postfix_expr INC_OP
    /// | postfix_expr DEC_OP
    /// ;
    fn postfix_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// argument_expr_list_opt
    /// : /* empty */
    /// | assignment_expr (',' assignment_expr)*
    /// ;
    fn argument_expr_list_opt(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }

    /// primary_expr
    /// : identifier
    /// | INT_CONSTANT
    /// | DOUBLE_CONSTANT
    /// | STRING_LITERAL
    /// | '(' expr ')'
    /// ;
    fn primary_expr(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }
}

impl Token {
    fn is_unary_operator(&self) -> bool {
        match self {
            Token::Ampersand
            | Token::Star
            | Token::Plus
            | Token::Minus
            | Token::BinaryNot
            | Token::LogicalNot => true,
            _ => false,
        }
    }
}
