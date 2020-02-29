use crate::data::lex::Literal;
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

pub use crate::data::ExprType as Expr;
pub use crate::data::StmtType as Stmt;
