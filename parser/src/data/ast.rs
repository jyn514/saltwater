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
    Cast(Box<Expr>),
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
