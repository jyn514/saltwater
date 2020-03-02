use std::fmt::{self, Display};

use crate::data::lex::{AssignmentToken, ComparisonToken, Literal, Locatable};
use crate::intern::InternedStr;

pub type Program = Vec<Declaration>;

pub enum ExternalDeclaration {
    Function(FunctionDefinition),
    Declaration(Declaration),
}

pub struct FunctionDefinition {
    specifiers: Vec<DeclarationSpecifier>,
    // TODO: maybe support K&R C?
    //DeclarationList
    declarator: Declarator,
    body: CompoundStatement,
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypeName {
    specifiers: Vec<DeclarationSpecifier>,
    declarator: Declarator,
}

// we don't _really_ need other specifiers
#[derive(Clone, Debug, PartialEq)]
pub enum DeclarationSpecifier {
    Const,
    Type(TypeSpecifier),
}

#[derive(Clone, Debug, PartialEq)]
pub enum TypeSpecifier {
    Void,
    Char,
    Short,
    Int,
    Long,
    Float,
    Double,
    Signed,
    Unsigned,
    Struct(StructSpecifier),
    Union(StructSpecifier),
    Enum(EnumSpecifier),
    Typedef(InternedStr),
}

#[derive(Clone, Debug, PartialEq)]
pub struct StructSpecifier {
    name: Option<InternedStr>,
    // Some([]): `struct s {}`
    // None: `struct s;`
    members: Option<Vec<Declaration>>,
}

// enum name? { A = 1, B = 2, C }
#[derive(Clone, Debug, PartialEq)]
pub struct EnumSpecifier {
    name: Option<InternedStr>,
    members: Vec<(InternedStr, Expr)>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declaration {
    specifiers: Vec<DeclarationSpecifier>,
    declarators: Vec<InitDeclarator>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct InitDeclarator {
    init: Option<Initializer>,
    declarator: Declarator,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Initializer {
    Scalar(Expr),
    Aggregate(Vec<Initializer>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Declarator {
    Pointer(Box<Declarator>),
    Array { of: Box<Declarator>, size: Box<Expr> },
    Id(InternedStr),
}

type CompoundStatement = Vec<Stmt>;

pub use crate::data::{Stmt, StmtType};
pub type Expr = Locatable<ExprType>;

#[derive(Clone, Debug, PartialEq)]
pub enum ExprType {
    // primary
    Id(InternedStr),
    Literal(Literal),

    // postfix
    FuncCall(Box<Expr>, Vec<Expr>),
    Member(Box<Expr>, InternedStr),
    // post increment/decrement
    PostIncrement(Box<Expr>, bool),

    // prefix
    PreIncrement(Box<Expr>, bool),
    Cast(TypeName, Box<Expr>),
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
    // &expr in static context
    // requires cooperation with the linker
    StaticRef(Box<Expr>),
    // used to work around various bugs, see places this is constructed for details
    Noop(Box<Expr>),
}

impl Display for TypeSpecifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use TypeSpecifier::*;
        match self {
            Void => write!(f, "void"),
            Char => write!(f, "char"),
            Short => write!(f, "short"),
            Int => write!(f, "int"),
            Long => write!(f, "long"),
            Float => write!(f, "float"),
            Double => write!(f, "double"),
            Signed => write!(f, "signed"),
            Unsigned => write!(f, "unsigned"),
        }
    }
}

impl Display for DeclarationSpecifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DeclarationSpecifier::Const => write!(f, "const"),
            DeclarationSpecifier::Type(ctype) => write!(f, "{}", ctype),
        }
    }
}


impl Declarator {
    fn print_pre(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Declarator::*;
        match self {
            Pointer(inner) | Array { .. } => inner.print_pre(f),
            //Function(ftype) => write!(f, "{}", ftype.return_type),
        }
    }
    fn print_mid(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
    fn print_post(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
}
impl Display for Declarator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.print_pre(f)?;
        self.print_mid(f)?;
        self.print_post(f)
        /*
        match self {
            Declarator::Id(id) => write!(f, "{}", id),
            Declarator::Array(of, size) => write!(f, "{}[{}]", of, size)
            Declarator::Pointer(inner) => {
                match *inner {
                    Declarator::Id(_) | Declarator::Pointer(_) => write!(f, "*{}", inner),
                    _ => write!(f, "(*){}", inner),
                }
            }
        }
        */
    }
}

impl Display for TypeName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for s in self.specifiers {
            write!(f, "{} ", s)?;
        }
        write!(f, "{}", self.declarator)
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
            ExprType::FuncCall(left, params) => write!(f, "({})({})", left, join(params)),
            ExprType::Cast(ctype, expr) => write!(f, "({})({})", ctype, expr),
            ExprType::SizeofType(ty) => write!(f, "sizeof({})", ty),
            ExprType::Member(compound, id) => write!(f, "({}).{}", compound, id),
            ExprType::PostIncrement(expr, inc) => {
                write!(f, "({}){}", expr, if *inc { "++" } else { "--" })
            }
            ExprType::StaticRef(expr) => write!(f, "&{}", expr),
            ExprType::Noop(expr) => write!(f, "{}", expr),
        }
    }
}
