use std::fmt::{self, Display};

use super::{joined, joined_locatable};
use crate::data::lex::{AssignmentToken, ComparisonToken, Literal, Locatable};
use crate::intern::InternedStr;

pub type Program = Vec<Declaration>;

#[derive(Clone, Debug, PartialEq)]
pub enum ExternalDeclaration {
    Function(FunctionDefinition),
    Declaration(Declaration),
}

#[derive(Clone, Debug, PartialEq)]
pub struct FunctionDefinition {
    pub specifiers: Vec<DeclarationSpecifier>,
    pub id: InternedStr,
    pub declarator: FunctionDeclarator,
    pub body: CompoundStatement,
}

impl FunctionDefinition {
    pub(crate) fn as_type(&self) -> TypeName {
        TypeName {
            specifiers: self.specifiers.clone(),
            declarator: Declarator {
                decl: DeclaratorType::Function(self.declarator.clone()),
                id: Some(self.id),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypeName {
    pub specifiers: Vec<DeclarationSpecifier>,
    pub declarator: Declarator,
}

#[derive(Clone, Debug, PartialEq)]
pub enum DeclarationSpecifier {
    Unit(UnitSpecifier),
    Struct(StructSpecifier),
    Union(StructSpecifier),
    // enum name? { A = 1, B = 2, C }
    Enum {
        name: Option<InternedStr>,
        members: Option<Vec<(InternedStr, Option<Expr>)>>,
    },
    // NOTE: _not_ the same as UnitSpecifier::Typedef
    // that represents the `typedef` keyword, this represents a name that has been typedef-ed
    Typedef(InternedStr),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum UnitSpecifier {
    // types
    Char,
    Short,
    Int,
    Long,
    Float,
    Double,
    Void,
    Signed,
    Unsigned,

    // weird types
    Bool,
    Complex,
    Imaginary,
    VaList,

    // qualifiers
    Const,
    Volatile,
    Restrict,
    // weird qualifiers
    Atomic,
    ThreadLocal,
    // function qualifiers
    Inline,
    NoReturn,

    // storage classes
    Auto,
    Register,
    Static,
    Extern,
    Typedef,
}

impl From<UnitSpecifier> for DeclarationSpecifier {
    fn from(unit: UnitSpecifier) -> Self {
        DeclarationSpecifier::Unit(unit)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct StructSpecifier {
    pub name: Option<InternedStr>,
    /// Some([]): `struct s {}`
    /// None: `struct s;`
    pub members: Option<Vec<StructDeclarationList>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct StructDeclarationList {
    pub specifiers: Vec<DeclarationSpecifier>,
    pub declarators: Vec<StructDeclarator>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct StructDeclarator {
    /// optional since this could be only padding bits
    pub decl: Option<Declarator>,
    pub bitfield: Option<Expr>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declaration {
    pub specifiers: Vec<DeclarationSpecifier>,
    pub declarators: Vec<Locatable<InitDeclarator>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct InitDeclarator {
    pub init: Option<Initializer>,
    pub declarator: Declarator,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Initializer {
    Scalar(Box<Expr>),
    Aggregate(Vec<Initializer>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declarator {
    pub decl: DeclaratorType,
    pub id: Option<InternedStr>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FunctionDeclarator {
    pub return_type: Box<DeclaratorType>,
    // TODO: maybe support K&R C?
    //DeclarationList
    pub params: Vec<TypeName>,
    pub varargs: bool,
}

impl From<FunctionDeclarator> for DeclaratorType {
    fn from(func: FunctionDeclarator) -> Self {
        DeclaratorType::Function(func)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum DeclaratorType {
    // No more declarator, e.g. for abstract params
    End,
    Pointer {
        to: Box<DeclaratorType>,
        qualifiers: Vec<DeclarationSpecifier>,
    },
    Array {
        of: Box<DeclaratorType>,
        size: Option<Box<Expr>>,
    },
    Function(FunctionDeclarator),
}

pub type Stmt = Locatable<StmtType>;
pub type CompoundStatement = Vec<Stmt>;

#[derive(Clone, Debug, PartialEq)]
pub enum StmtType {
    Compound(CompoundStatement),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    Do(Box<Stmt>, Expr),
    While(Expr, Box<Stmt>),
    // for(int i = 1, j = 2; i < 4; ++i) body
    // for(i = 1; ; ++i) body
    // for (;;) ;
    For {
        initializer: Box<Stmt>,
        condition: Option<Box<Expr>>,
        post_loop: Option<Box<Expr>>,
        body: Box<Stmt>,
    },
    Switch(Expr, Box<Stmt>),
    Label(InternedStr, Box<Stmt>),
    Case(Box<Expr>, Box<Stmt>),
    Default(Box<Stmt>),
    Expr(Expr),
    Goto(InternedStr),
    Continue,
    Break,
    Return(Option<Expr>),
    Decl(Declaration),
}

pub type Expr = Locatable<ExprType>;

#[derive(Clone, Debug, PartialEq)]
pub enum ExprType {
    // primary
    Id(InternedStr),
    Literal(Literal),

    // postfix
    FuncCall(Box<Expr>, Vec<Expr>),
    Member(Box<Expr>, InternedStr),
    DerefMember(Box<Expr>, InternedStr),
    // post increment/decrement
    PostIncrement(Box<Expr>, bool),
    // a[i]
    Index(Box<Expr>, Box<Expr>),

    // prefix
    PreIncrement(Box<Expr>, bool),
    Cast(TypeName, Box<Expr>),
    AlignofType(TypeName),
    AlignofExpr(Box<Expr>),
    SizeofType(TypeName),
    SizeofExpr(Box<Expr>),
    Deref(Box<Expr>),
    AddressOf(Box<Expr>),
    UnaryPlus(Box<Expr>),
    Negate(Box<Expr>),
    BitwiseNot(Box<Expr>),
    LogicalNot(Box<Expr>),

    // binary
    LogicalOr(Box<Expr>, Box<Expr>),
    BitwiseOr(Box<Expr>, Box<Expr>),
    LogicalAnd(Box<Expr>, Box<Expr>),
    BitwiseAnd(Box<Expr>, Box<Expr>),
    Xor(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    // bool: left or right
    Shift(Box<Expr>, Box<Expr>, bool),
    // Token: make >, <, <=, ... part of the same variant
    Compare(Box<Expr>, Box<Expr>, ComparisonToken),
    // Token: allow extended assignment
    Assign(Box<Expr>, Box<Expr>, AssignmentToken),

    // misfits
    // Ternary: if ? then : else
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
    Comma(Box<Expr>, Box<Expr>),
}

impl Default for StmtType {
    fn default() -> Self {
        StmtType::Compound(Vec::new())
    }
}

impl Display for StructSpecifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(ident) = self.name {
            write!(f, "{} ", ident)
        } else if let Some(body) = &self.members {
            writeln!(f, "{{")?;
            for decl in body {
                writeln!(f, "{}{}", INDENT, decl)?;
            }
            write!(f, "}}")
        } else {
            // what are we supposed to do for `struct;` lol
            Ok(())
        }
    }
}

impl Display for StructDeclarationList {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ", joined(&self.specifiers, " "))?;
        write!(f, "{};", joined(&self.declarators, ", "))
    }
}

impl Display for StructDeclarator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(decl) = &self.decl {
            write!(f, "{}", decl)?;
        }
        if let Some(expr) = &self.bitfield {
            write!(f, ":{}", expr)?;
        }
        Ok(())
    }
}

impl Display for ExternalDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExternalDeclaration::Declaration(decl) => write!(f, "{}", decl),
            ExternalDeclaration::Function(func) => write!(f, "{}", func),
        }
    }
}

impl Display for FunctionDefinition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for spec in &self.specifiers {
            write!(f, "{} ", spec)?;
        }
        self.declarator.pretty_print(Some(self.id), f)?;
        pretty_print_compound(f, &self.body, 0)
    }
}

impl Display for Declaration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let specs = joined(&self.specifiers, " ");
        write!(f, "{}", specs)?;
        if !specs.is_empty() {
            write!(f, " ")?;
        }
        write!(f, "{};", joined_locatable(&self.declarators, ", "))
    }
}

impl Display for InitDeclarator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.declarator)?;
        if let Some(init) = &self.init {
            write!(f, " = {}", init)?;
        }
        Ok(())
    }
}

impl Display for Initializer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Initializer::Scalar(expr) => write!(f, "{}", expr),
            Initializer::Aggregate(items) => {
                write!(f, "{{ ")?;
                write!(f, "{}", joined(items, ", "))?;
                write!(f, " }}")
            }
        }
    }
}

impl Display for DeclarationSpecifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use DeclarationSpecifier::*;

        match self {
            Unit(u) => write!(f, "{}", u),
            Enum {
                name: Some(ident), ..
            } => write!(f, "enum {}", ident),
            // error, but caught later
            Enum {
                name: None,
                members: None,
            } => write!(f, "enum;"),
            Enum {
                name: None,
                members: Some(members),
            } => {
                let members = members.iter().map(|(name, value)| {
                    let val = if let Some(val) = value {
                        format!(" = {}", val)
                    } else {
                        String::new()
                    };
                    format!("{}{}", name, val)
                });
                write!(f, "enum {{ {} }}", joined(members, ", "))
            }
            Union(spec) => write!(f, "union {}", spec),
            Struct(spec) => write!(f, "struct {}", spec),
            Typedef(name) => write!(f, "{}", name),
        }
    }
}

impl Display for UnitSpecifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use UnitSpecifier::*;

        match self {
            Static => write!(f, "static"),
            Extern => write!(f, "extern"),
            Register => write!(f, "register"),
            Auto => write!(f, "auto"),
            Typedef => write!(f, "typedef"),

            Const => write!(f, "const"),
            Volatile => write!(f, "volatile"),
            Restrict => write!(f, "restrict"),
            Atomic => write!(f, "_Atomic"),
            ThreadLocal => write!(f, "_Thread_local"),

            Inline => write!(f, "inline"),
            NoReturn => write!(f, "_Noreturn"),

            Void => write!(f, "void"),
            Bool => write!(f, "_Bool"),
            Char => write!(f, "char"),
            Short => write!(f, "short"),
            Int => write!(f, "int"),
            Long => write!(f, "long"),
            Float => write!(f, "float"),
            Double => write!(f, "double"),
            Signed => write!(f, "signed"),
            Unsigned => write!(f, "unsigned"),

            Complex => write!(f, "_Complex"),
            Imaginary => write!(f, "_Imaginary"),
            VaList => write!(f, "va_list"),
        }
    }
}

impl Declarator {
    fn is_nonempty(&self) -> bool {
        match self.decl {
            DeclaratorType::End => self.id.is_some(),
            _ => true,
        }
    }
}

impl DeclaratorType {
    fn pretty_print(&self, name: Option<InternedStr>, f: &mut fmt::Formatter) -> fmt::Result {
        self.print_pre(f)?;
        self.print_mid(name, f)?;
        self.print_post(f)
    }
    fn print_pre(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use DeclaratorType::*;
        match self {
            Pointer { to: inner, .. } | Array { of: inner, .. } => inner.print_pre(f),
            Function(FunctionDeclarator { return_type, .. }) => write!(f, "{}", return_type),
            End => Ok(()),
        }
    }
    fn print_mid(&self, name: Option<InternedStr>, f: &mut fmt::Formatter) -> fmt::Result {
        use DeclaratorType::*;

        match self {
            Pointer { to, qualifiers } => {
                to.print_mid(None, f)?;
                let qs = joined(qualifiers, " ");
                // we need to handle the following cases:
                // `(*const p)()`
                // `*const p`
                // `*const (*p)()`
                // `(*const)` (e.g. in an abstract parameter)
                // `*p` (in any of the above contexts)
                let name = name.unwrap_or_default();
                let pointer = if !qs.is_empty() && name != Default::default() {
                    format!("*{} {}", qs, name)
                } else {
                    format!("*{}{}", qs, name)
                };
                match **to {
                    Array { .. } | Function { .. } => write!(f, "({})", pointer),
                    // this is the only case when `*const (*p)()` can occur
                    // TODO: maybe put a space after the qualifier if it's there?
                    // clang-format disagrees with me about the space though
                    End => write!(f, "{}", pointer),
                    Pointer { .. } => write!(f, "{}", pointer),
                }
            }
            Array { of, .. } => of.print_mid(name, f),
            End | Function { .. } => {
                if let Some(name) = name {
                    write!(f, "{}", name)?;
                }
                Ok(())
            }
        }
    }
    fn print_post(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use DeclaratorType::*;
        match self {
            Pointer { to, .. } => to.print_post(f),
            Array { of, size } => {
                write!(f, "[")?;
                if let Some(expr) = size {
                    write!(f, "{}", expr)?;
                }
                write!(f, "]")?;
                of.print_post(f)
            }
            Function(FunctionDeclarator {
                params, varargs, ..
            }) => {
                write!(f, "({}", joined(params, ", "))?;
                if *varargs {
                    write!(f, ", ...")?;
                }
                write!(f, ")")
            }
            End => Ok(()),
        }
    }
}

impl Display for Declarator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.decl.pretty_print(self.id, f)
    }
}

impl Display for FunctionDeclarator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.pretty_print(None, f)
    }
}

impl FunctionDeclarator {
    fn pretty_print(&self, name: Option<InternedStr>, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO: maybe factor out some of the repeated code?
        // print_pre
        write!(f, "{}", self.return_type)?;
        // print_mid
        if let Some(name) = name {
            write!(f, "{}", name)?;
        }
        // print_post
        write!(f, "({}", joined(&self.params, ", "))?;
        if self.varargs {
            write!(f, ", ...")?;
        }
        write!(f, ")")
    }
}

impl Display for DeclaratorType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // declarator with no id
        self.pretty_print(None, f)
    }
}

impl Display for TypeName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", joined(&self.specifiers, " "))?;
        if self.declarator.is_nonempty() {
            write!(f, " {}", self.declarator)?;
        }
        Ok(())
    }
}

impl Display for StmtType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.pretty_print(f, 0)
    }
}

const INDENT: &str = "    ";

fn pretty_print_compound(f: &mut fmt::Formatter, stmts: &[Stmt], depth: usize) -> fmt::Result {
    // NOTE: expects the caller to have already printed the leading whitespace
    writeln!(f, "{{")?;
    for stmt in stmts {
        stmt.data.pretty_print(f, depth + 1)?;
        writeln!(f)?;
    }
    write!(f, "{}}}", INDENT.repeat(depth))
}

impl StmtType {
    fn pretty_print(&self, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        write!(f, "{}", INDENT.repeat(depth))?;
        match self {
            StmtType::Expr(expr) => write!(f, "{};", expr),
            StmtType::Return(None) => write!(f, "return;"),
            StmtType::Return(Some(expr)) => write!(f, "return {};", expr),
            StmtType::Break => write!(f, "break;"),
            StmtType::Continue => write!(f, "continue;"),
            StmtType::Default(stmt) => {
                writeln!(f, "default:")?;
                stmt.data.pretty_print(f, depth + 1)
            }
            StmtType::Case(expr, stmt) => {
                writeln!(f, "case {}:", expr)?;
                stmt.data.pretty_print(f, depth + 1)
            }
            StmtType::Goto(id) => write!(f, "goto {};", id),
            StmtType::Label(id, inner) => write!(f, "{}: {}", id, inner.data),
            StmtType::While(condition, body) => write!(f, "while ({}) {}", condition, body.data),
            StmtType::If(condition, body, None) => write!(f, "if ({}) {}", condition, body.data),
            StmtType::If(condition, body, Some(otherwise)) => write!(
                f,
                "if ({}) {} else {}",
                condition, body.data, otherwise.data
            ),
            StmtType::Do(body, condition) => write!(f, "do {} while ({});", body.data, condition),
            StmtType::For {
                initializer: decls,
                condition,
                post_loop,
                body,
            } => {
                write!(f, "for (")?;
                match &decls.data {
                    StmtType::Decl(decls) => write!(f, "{} ", decls)?,
                    StmtType::Expr(expr) => write!(f, "{}; ", expr)?,
                    StmtType::Compound(compound) if compound.is_empty() => write!(f, ";")?,
                    _ => unreachable!("for loop initialization other than decl or expr"),
                };
                match condition {
                    Some(condition) => write!(f, "{};", condition)?,
                    None => write!(f, ";")?,
                };
                match post_loop {
                    Some(condition) => write!(f, " {}) ", condition)?,
                    None => write!(f, ") ")?,
                };
                // don't increase depth in case it's on the same line
                body.data.pretty_print(f, depth)
            }
            StmtType::Decl(decls) => write!(f, "{}", decls),
            StmtType::Compound(stmts) => pretty_print_compound(f, stmts, depth),
            StmtType::Switch(condition, body) => write!(f, "switch ({}) {}", condition, body.data),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.data {
            ExprType::Comma(left, right) => write!(f, "{}, {}", *left, *right),
            ExprType::Literal(token) => write!(f, "{}", token),
            ExprType::Id(symbol) => write!(f, "{}", symbol),
            ExprType::Add(left, right) => write!(f, "({}) + ({})", left, right),
            ExprType::Sub(left, right) => write!(f, "({}) - ({})", left, right),
            ExprType::Mul(left, right) => write!(f, "({}) * ({})", left, right),
            ExprType::Div(left, right) => write!(f, "({}) / ({})", left, right),
            ExprType::Mod(left, right) => write!(f, "({}) % ({})", left, right),
            ExprType::Xor(left, right) => write!(f, "({}) ^ ({})", left, right),
            ExprType::BitwiseOr(left, right) => write!(f, "({}) | ({})", left, right),
            ExprType::BitwiseAnd(left, right) => write!(f, "({}) & ({})", left, right),
            ExprType::BitwiseNot(expr) => write!(f, "(~{})", expr),
            ExprType::Deref(expr) => write!(f, "*({})", expr),
            ExprType::Negate(expr) => write!(f, "-({})", expr),
            ExprType::UnaryPlus(expr) => write!(f, "+({})", expr),
            ExprType::LogicalNot(expr) => write!(f, "!({})", expr),
            ExprType::LogicalOr(left, right) => write!(f, "({}) || ({})", left, right),
            ExprType::LogicalAnd(left, right) => write!(f, "({}) && ({})", left, right),
            ExprType::Shift(val, by, left) => {
                write!(f, "({}) {} ({})", val, if *left { "<<" } else { ">>" }, by)
            }
            ExprType::Compare(left, right, token) => write!(f, "({}) {} ({})", left, token, right),
            ExprType::Assign(left, right, token) => write!(f, "({}) {} ({})", left, token, right),
            ExprType::Ternary(cond, left, right) => {
                write!(f, "({}) ? ({}) : ({})", cond, left, right)
            }
            ExprType::FuncCall(left, params) => write!(f, "({})({})", left, joined(params, ", ")),
            ExprType::Cast(ctype, expr) => write!(f, "({})({})", ctype, expr),
            ExprType::Member(compound, id) => write!(f, "({}).{}", compound, id),
            ExprType::DerefMember(compound, id) => write!(f, "({})->{}", compound, id),
            ExprType::PreIncrement(expr, inc) => {
                write!(f, "{}({})", if *inc { "++" } else { "--" }, expr)
            }
            ExprType::PostIncrement(expr, inc) => {
                write!(f, "({}){}", expr, if *inc { "++" } else { "--" })
            }
            ExprType::Index(array, index) => write!(f, "({})[{}]", array, index),
            // intrinsics
            ExprType::AddressOf(expr) => write!(f, "&({})", expr),
            ExprType::SizeofExpr(expr) => write!(f, "sizeof({})", expr),
            ExprType::SizeofType(ty) => write!(f, "sizeof({})", ty),
            ExprType::AlignofExpr(expr) => write!(f, "alignof({})", expr),
            ExprType::AlignofType(ty) => write!(f, "alignof({})", ty),
        }
    }
}
