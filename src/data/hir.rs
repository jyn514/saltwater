use derive_more::Display;

use std::cell::RefCell;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;
use std::rc::Rc;

#[cfg(test)]
use proptest_derive::Arbitrary;

use super::lex::{ComparisonToken, Keyword, Literal, Locatable};
use super::types::Type;
use super::*;
use crate::intern::InternedStr;

pub type Stmt = Locatable<StmtType>;

#[derive(Clone, Debug, PartialEq)]
#[allow(clippy::large_enum_variant)]
pub enum StmtType {
    Compound(Vec<Stmt>),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    Do(Box<Stmt>, Expr),
    While(Expr, Box<Stmt>),
    // for(int i = 1, j = 2; i < 4; ++i) body
    // for(i = 1; ; ++i) body
    // for (;;) ;
    For(Box<Stmt>, Option<Box<Expr>>, Option<Box<Expr>>, Box<Stmt>),
    Switch(Expr, Box<Stmt>),
    Label(InternedStr, Box<Stmt>),
    Case(u64, Box<Stmt>),
    Default(Box<Stmt>),
    Expr(Expr),
    Goto(InternedStr),
    Continue,
    Break,
    Return(Option<Expr>),
    Decl(Vec<Locatable<Declaration>>),
}

impl Default for StmtType {
    fn default() -> Self {
        StmtType::Compound(Vec::new())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declaration {
    pub symbol: MetadataRef,
    pub init: Option<Initializer>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Initializer {
    Scalar(Box<Expr>),                 // int i = 5;
    InitializerList(Vec<Initializer>), // int a[] = { 1, 2, 3 };
    FunctionBody(Vec<Stmt>),           // int f() { return 0; }
}

/// Holds the metadata for an expression.
#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    /// expr: holds the actual expression
    pub expr: ExprType,

    /// ctype: holds the type of the expression
    pub ctype: Type,

    /// lval: whether an expression can be assigned to
    ///
    /// for example, variables, array elements, and pointer dereferences are lvals,
    /// but literals, functions, and addresses are not
    pub lval: bool,

    /// location: the best approximation of where the expression is
    ///
    /// usually points to the location of the operation symbol, or the literal if no
    /// operations is being performed
    /// implicit operations should point to the child expression
    pub location: Location,
}

/// An identifier used to look up the metadata for a variable.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct MetadataRef(usize);

thread_local!(
    /// The global storage for all metadata.
    ///
    /// The type is read like so:
    /// RefCell: A container with interior mutability, used because `LocalKey`
    /// returns an immutable reference.
    /// MetadataStore: metadata for all variables seen so far
    static METADATA_STORE: RefCell<MetadataStore> = Default::default()
);

#[derive(Default)]
struct MetadataStore(Vec<Rc<Metadata>>);

impl MetadataStore {
    fn insert(&mut self, m: Metadata) -> MetadataRef {
        let i = self.0.len();
        self.0.push(Rc::new(m));
        MetadataRef(i)
    }
    /// Guaranteed not to panic since `MetadataRef` is always valid
    pub(crate) fn get(&self, i: MetadataRef) -> Rc<Metadata> {
        self.0[i.0].clone()
    }
}

impl MetadataRef {
    pub fn get(self) -> Rc<Metadata> {
        METADATA_STORE.with(|store| store.borrow().get(self))
    }
}

impl Metadata {
    pub(crate) fn insert(self) -> MetadataRef {
        METADATA_STORE.with(|store| store.borrow_mut().insert(self))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprType {
    // primary expressions
    // This stores a reference to the metadata for the identifier,
    // which can be looked up using a `metadata_store`.
    Id(MetadataRef),
    Literal(Literal),
    FuncCall(Box<Expr>, Vec<Expr>),
    Member(Box<Expr>, InternedStr),

    // unary expressions
    // post increment/decrement
    PostIncrement(Box<Expr>, bool),
    Cast(Box<Expr>),
    Sizeof(Type),
    Deref(Box<Expr>),
    Negate(Box<Expr>),
    BitwiseNot(Box<Expr>),

    // binary expressions
    Binary(BinaryOp, Box<Expr>, Box<Expr>),

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

#[derive(Copy, Clone, Debug, PartialEq, Eq, Display)]
pub enum BinaryOp {
    // binary expressions
    #[display(fmt = "||")]
    LogicalOr,
    #[display(fmt = "|")]
    BitwiseOr,
    #[display(fmt = "&&")]
    LogicalAnd,
    #[display(fmt = "&")]
    BitwiseAnd,
    #[display(fmt = "^")]
    Xor,
    #[display(fmt = "*")]
    Mul,
    #[display(fmt = "/")]
    Div,
    #[display(fmt = "%")]
    Mod,
    #[display(fmt = "+")]
    Add,
    #[display(fmt = "-")]
    Sub,
    #[display(fmt = "<<")]
    Shl,
    #[display(fmt = "<<")]
    Shr,
    // Token: make >, <, <=, ... part of the same variant
    Compare(ComparisonToken),
    #[display(fmt = "=")]
    Assign,
}

impl Expr {
    pub fn into_literal(self) -> Result<Literal, Expr> {
        match self.expr {
            ExprType::Literal(lit) => Ok(lit),
            _ => Err(self),
        }
    }
    pub fn is_constexpr(&self) -> bool {
        match &self.expr {
            ExprType::Literal(_) => true,
            _ => false,
        }
    }
}

/* structs */
/// The metadata stored for variables and function parameters.
///
/// For abstract function parameters, e.g. `int f(int)`, the `id` will resolve to the empty string.
/// Furthermore, it is guaranteed to be equal to `InternedStr::default()`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Metadata {
    pub ctype: Type,
    pub storage_class: StorageClass,
    pub qualifiers: Qualifiers,
    pub id: InternedStr,
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Arbitrary))]
pub struct Qualifiers {
    pub volatile: bool,
    pub c_const: bool,
    pub func: FunctionQualifiers,
}

#[cfg_attr(test, derive(Arbitrary))]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct FunctionQualifiers {
    pub inline: bool,
    pub no_return: bool,
}

#[derive(Debug)]
pub(crate) struct Scope<K: Hash + Eq, V>(Vec<HashMap<K, V>>);

impl Qualifiers {
    pub(crate) fn has_func_qualifiers(self) -> bool {
        self.func.inline || self.func.no_return
    }
    pub(crate) const NONE: Qualifiers = Qualifiers {
        c_const: false,
        volatile: false,
        func: FunctionQualifiers {
            inline: false,
            no_return: false,
        },
    };
}

impl Display for FunctionQualifiers {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match (self.inline, self.no_return) {
            (true, true) => write!(f, "{} {}", Keyword::Inline, Keyword::NoReturn),
            (true, false) => write!(f, "{}", Keyword::NoReturn),
            (false, true) => write!(f, "{}", Keyword::NoReturn),
            (false, false) => Ok(()),
        }
    }
}

impl<K: Hash + Eq, V> Scope<K, V> {
    #[inline]
    pub(crate) fn new() -> Self {
        Self(vec![HashMap::new()])
    }
    #[inline]
    pub(crate) fn enter(&mut self) {
        self.0.push(HashMap::<K, V>::new())
    }
    #[inline]
    pub(crate) fn exit(&mut self) {
        self.0.pop();
    }
    pub(crate) fn get(&self, name: &K) -> Option<&V> {
        self.iter()
            .filter_map(|(key, value)| if key == name { Some(value) } else { None })
            .next()
    }
    // returns whether the _immediate_ scope contains `name`
    #[inline]
    pub(crate) fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.0.last_mut().unwrap().insert(key, value)
    }
    #[inline]
    pub(crate) fn get_immediate(&self, name: &K) -> Option<&V> {
        self.0.last().unwrap().get(name)
    }
    #[inline]
    pub(crate) fn get_all_immediate(&mut self) -> &mut HashMap<K, V> {
        self.0.last_mut().unwrap()
    }
    pub(crate) fn is_global(&self) -> bool {
        self.0.len() == 1
    }
    pub(crate) fn _remove(&mut self, key: &K) -> Option<V> {
        debug_assert!(!self.0.is_empty());
        self.0.last_mut().unwrap().remove(key)
    }
    pub(crate) fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.0.iter().rev().flatten()
    }
}

impl<K: Eq + Hash, V> Default for Scope<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl TryFrom<Keyword> for StorageClass {
    type Error = Keyword;
    fn try_from(value: Keyword) -> Result<StorageClass, Keyword> {
        use StorageClass::*;
        match value {
            Keyword::Extern => Ok(Extern),
            Keyword::Static => Ok(Static),
            Keyword::Auto => Ok(Auto),
            Keyword::Register => Ok(Register),
            Keyword::Typedef => Ok(Typedef),
            _ => Err(value),
        }
    }
}

impl Default for StorageClass {
    fn default() -> StorageClass {
        StorageClass::Auto
    }
}

impl Display for StorageClass {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", &format!("{:?}", self).to_lowercase())
    }
}

impl Display for Qualifiers {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match (self.c_const, self.volatile) {
                (true, true) => "const volatile",
                (true, false) => "const",
                (false, true) => "volatile",
                (false, false) => "",
            }
        )
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.expr {
            ExprType::Comma(left, right) => write!(f, "{}, {}", *left, *right),
            ExprType::Literal(token) => write!(f, "{}", token),
            ExprType::Id(symbol) => write!(f, "{}", symbol.get().id),
            ExprType::Binary(op, left, right) => write!(f, "({}) {} ({})", left, op, right),
            ExprType::BitwiseNot(expr) => write!(f, "(~{})", expr),
            ExprType::Deref(expr) => write!(f, "*({})", expr),
            ExprType::Negate(expr) => write!(f, "-({})", expr),

            ExprType::Ternary(cond, left, right) => {
                write!(f, "({}) ? ({}) : ({})", cond, left, right)
            }
            ExprType::FuncCall(left, params) => write!(f, "({})({})", left, joined(params, ", ")),
            ExprType::Cast(expr) => write!(f, "({})({})", self.ctype, expr),
            ExprType::Sizeof(ty) => write!(f, "sizeof({})", ty),
            ExprType::Member(compound, id) => write!(f, "({}).{}", compound, id),
            ExprType::PostIncrement(expr, inc) => {
                write!(f, "({}){}", expr, if *inc { "++" } else { "--" })
            }
            ExprType::StaticRef(expr) => write!(f, "&{}", expr),
            ExprType::Noop(expr) => write!(f, "{}", expr),
        }
    }
}

impl Display for Initializer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Initializer::Scalar(expr) => write!(f, "{}", expr),
            Initializer::InitializerList(list) => {
                write!(f, "{{ ")?;
                write!(f, "{}", joined(list, ", "),)?;
                write!(f, " }}")
            }
            Initializer::FunctionBody(body) => {
                writeln!(f, "{{")?;
                for stmt in body {
                    writeln!(f, "{}", stmt.data)?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl Display for StmtType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.pretty_print(f, 0)
    }
}

impl StmtType {
    fn pretty_print(&self, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        write!(f, "{}", "    ".repeat(depth))?;
        match self {
            StmtType::Expr(expr) => write!(f, "{};", expr),
            StmtType::Return(None) => write!(f, "return;"),
            StmtType::Return(Some(expr)) => write!(f, "return {};", expr),
            StmtType::Break => write!(f, "break;"),
            StmtType::Continue => write!(f, "continue;"),
            StmtType::Default(stmt) => write!(f, "default:\n{}", stmt.data),
            StmtType::Case(expr, stmt) => write!(f, "case {}:\n{}", expr, stmt.data),
            StmtType::Goto(id) => write!(f, "goto {};", id),
            StmtType::Label(id, inner) => write!(f, "{}: {}", id, inner.data),
            StmtType::While(condition, body) => write!(f, "while ({}) {}", condition, body.data),
            StmtType::If(condition, body, None) => write!(f, "if ({}) {}", condition, body.data),
            StmtType::If(condition, body, Some(otherwise)) => write!(
                f,
                "if ({}) {} else {}",
                condition, body.data, otherwise.data
            ),
            StmtType::Do(body, condition) => {
                write!(f, "do {:?} while ({:?});", body.data, condition)
            }
            StmtType::For(decls, condition, post_loop, body) => {
                write!(f, "for (")?;
                match &decls.data {
                    StmtType::Decl(decls) => {
                        let len = decls.len();
                        for (i, decl) in decls.iter().enumerate() {
                            write!(f, "{}", decl.data)?;
                            if i != len - 1 {
                                write!(f, ", ")?;
                            }
                        }
                    }
                    StmtType::Expr(expr) => write!(f, "{}", expr)?,
                    _ => unreachable!("for loop initialization other than decl or expr"),
                }
                match condition {
                    Some(condition) => write!(f, "; {}; ", condition)?,
                    None => write!(f, "; ; ")?,
                };
                match post_loop {
                    Some(condition) => write!(f, " {})", condition)?,
                    None => write!(f, ")")?,
                };
                write!(f, " {}", body.data)
            }
            StmtType::Decl(decls) => {
                for decl in decls {
                    writeln!(f, "{};", decl.data)?;
                }
                Ok(())
            }
            StmtType::Compound(stmts) => {
                writeln!(f, "{{")?;
                for stmt in stmts {
                    writeln!(f, "{}", stmt.data)?;
                }
                write!(f, "}}")
            }
            StmtType::Switch(condition, body) => write!(f, "switch ({}) {}", condition, body.data),
        }?;
        writeln!(f)
    }
}

impl Display for Metadata {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.qualifiers != Qualifiers::default() {
            write!(f, "{} ", self.qualifiers)?;
        }
        write!(f, "{} ", self.storage_class)?;
        super::types::print_type(&self.ctype, Some(self.id), f)
    }
}

impl Display for Declaration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.symbol.get())?;
        match &self.init {
            Some(Initializer::FunctionBody(body)) => {
                writeln!(f, " {{")?;
                for stmt in body {
                    stmt.data.pretty_print(f, 1)?;
                }
                writeln!(f, "}}")
            }
            Some(Initializer::Scalar(expr)) => write!(f, " = {};", expr),
            Some(Initializer::InitializerList(inits)) => {
                write!(f, " = {{")?;
                for init in inits {
                    write!(f, "{}, ", init)?;
                }
                write!(f, "}};")
            }
            None => write!(f, ";"),
        }
    }
}

/*
impl PartialEq for Symbol {
    // don't require both symbols to be `init` to be equal
    fn eq(&self, other: &Self) -> bool {
        self.ctype == other.ctype
            && self.id == other.id
            && self.qualifiers == other.qualifiers
            && (self.storage_class == other.storage_class
                || !self.ctype.is_function()
                    && (self.storage_class == StorageClass::Auto
                        && other.storage_class == StorageClass::Extern
                        || self.storage_class == StorageClass::Extern
                            && other.storage_class == StorageClass::Auto))
    }
}

impl Eq for Symbol {}
*/

#[cfg(test)]
mod tests {
    use crate::parse::test::parser;

    #[test]
    fn type_display() {
        let types = [
            "int",
            "int *",
            "int [1][2][3]",
            "char *(*)(float)",
            "short *(*)[1][2][3]",
            "_Bool",
            "struct s",
        ];
        for ty in types.iter() {
            let parsed_ty = parser(dbg!(ty)).type_name().unwrap().data;
            assert_eq!(parsed_ty.to_string().trim(), *ty);
        }
    }
}
