#![allow(unused_variables)]

use std::collections::{HashMap, VecDeque};

use counter::Counter;

use crate::data::{self, error::Warning, hir::*, *};
use crate::intern::InternedStr;

pub(crate) type TagScope = Scope<InternedStr, TagEntry>;
type Parser = super::Parser<super::Lexer>;
type SemanticResult<T> = Result<T, Locatable<SemanticError>>;

#[derive(Clone, Debug)]
pub(crate) enum TagEntry {
    Struct(StructRef),
    Union(StructRef),
    // list of (name, value)s
    Enum(Vec<(InternedStr, i64)>),
}

pub struct Analyzer {
    declarations: Parser,
    // in case a `Declaration` has multiple declarators
    pending: VecDeque<Locatable<Declaration>>,
    /// objects that are in scope
    /// C actually has 4 different scopes:
    /// 1. ordinary identifiers
    /// 2. tags
    /// 3. label names
    /// 4. members
    ///
    /// This holds the scope for ordinary identifiers: variables and typedefs
    scope: Scope<InternedStr, MetadataRef>,
    /// the compound types that have been declared (struct/union/enum)
    /// scope 2. from above
    tag_scope: TagScope,
    /// Internal API which makes it easier to return errors lazily
    error_handler: ErrorHandler,
}

impl Iterator for Analyzer {
    type Item = CompileResult<Locatable<Declaration>>;
    fn next(&mut self) -> Option<Self::Item> {
        // have to handle `int;` somehow
        loop {
            // Instead of returning `SemanticResult`, the analyzer puts all errors into `error_handler`.
            // This simplifies the logic in `next` greatly.
            // NOTE: this returns errors for a declaration before the declaration itself
            if let Some(err) = self.error_handler.pop_front() {
                return Some(Err(err));
            // If we saw `int i, j, k;`, we treated those as different declarations
            // `j, k` will be stored into `pending`
            } else if let Some(decl) = self.pending.pop_front() {
                return Some(Ok(decl));
            }
            // Now do the real work.
            let next = match self.declarations.next()? {
                Err(err) => return Some(Err(err)),
                Ok(decl) => decl,
            };
            // Note that we need to store `next` so that we have the location in case it was empty.
            let location = next.location;
            let decls = self.parse_declaration(next);
            if decls.is_empty() {
                self.error_handler.warn(Warning::EmptyDeclaration, location);
            } else {
                // TODO: if an error occurs, should we still add the declaration to `pending`?
                self.pending.extend(decls);
            }
        }
    }
}

impl Analyzer {
    pub fn new(parser: Parser) -> Self {
        Self {
            declarations: parser,
            error_handler: ErrorHandler::new(),
            scope: Scope::new(),
            tag_scope: Scope::new(),
            pending: VecDeque::new(),
        }
    }
    fn parse_declaration(
        &mut self, next: Locatable<ast::ExternalDeclaration>,
    ) -> Vec<Locatable<Declaration>> {
        use ast::ExternalDeclaration;

        match next.data {
            ExternalDeclaration::Function(func) => {
                let id = func.id;
                let (meta_ref, body) = FunctionAnalyzer::analyze(func, self, next.location);
                self.scope.insert(id, meta_ref);
                let decl = Declaration {
                    symbol: meta_ref,
                    init: Some(Initializer::FunctionBody(body)),
                };
                vec![Locatable::new(decl, next.location)]
            }
            ExternalDeclaration::Declaration(declaration) => {
                let original = self.parse_specifiers(declaration.specifiers, next.location);
                // `int i;` desugars to `extern int i;` at global scope,
                // but to `auto int i;` at function scope
                let sc = original.storage_class.unwrap_or_else(|| {
                    if self.scope.is_global() {
                        StorageClass::Extern
                    } else {
                        StorageClass::Auto
                    }
                });
                if sc == StorageClass::Auto && self.scope.is_global() {
                    self.error_handler
                        .error(SemanticError::AutoAtGlobalScope, next.location);
                }
                let mut decls = Vec::new();
                for d in declaration.declarators {
                    let ctype = self.parse_declarator(
                        original.ctype.clone(),
                        d.data.declarator.decl,
                        d.location,
                    );
                    let id = d.data.declarator.id;
                    let id = id.expect("declarations should never be abstract");
                    let init = if let Some(init) = d.data.init {
                        Some(self.parse_initializer(init, &ctype, d.location))
                    } else {
                        None
                    };
                    let meta = Metadata {
                        ctype,
                        id,
                        qualifiers: original.qualifiers,
                        storage_class: sc,
                    }
                    .insert();
                    decls.push(Locatable::new(
                        Declaration { symbol: meta, init },
                        d.location,
                    ));
                }
                decls
            }
        }
    }
    fn parse_type(
        &mut self, specifiers: Vec<ast::DeclarationSpecifier>, declarator: ast::DeclaratorType,
        location: Location,
    ) -> ParsedType {
        let mut specs = self.parse_specifiers(specifiers, location);
        specs.ctype = self.parse_declarator(specs.ctype, declarator, location);
        specs
    }
    fn parse_specifiers(
        &mut self, specifiers: Vec<ast::DeclarationSpecifier>, location: Location,
    ) -> ParsedType {
        use ast::{DeclarationSpecifier::*, UnitSpecifier::*};
        use std::collections::HashSet;
        // need to parse specifiers now
        // it's not enough to collect into a `Set` since `long long` has a different meaning than `long`
        // instead, we see how many times each specifier is present
        // however, for some specifiers this doesn't really make sense:
        // if we see `struct s { int i; }` twice in a row,
        // it's more likely that the user forgot a semicolon in between than try to make some weird double struct type.
        // so: count the specifiers that are keywords and store the rest somewhere out of the way

        // TODO: initialization is a mess
        let (counter, compounds) = count_specifiers(specifiers, &mut self.error_handler, location);
        // Now that we've separated this into unit specifiers and compound specifiers,
        // see if we can pick up the proper types and qualifiers.
        let signed = match (counter.get(&Signed), counter.get(&Unsigned)) {
            (None, None) | (Some(_), None) => true,
            (None, Some(_)) => false,
            (Some(_), Some(_)) => {
                self.error_handler
                    .error(SemanticError::ConflictingSigned, location);
                true
            }
        };
        // `long` is special because of `long long`
        let mut ctype = None;
        if let Some(&long_count) = counter.get(&Long) {
            match long_count {
                0 => panic!("constraint violation, should only set count if > 0"),
                1 => ctype = Some(Type::Long(signed)),
                2 => unimplemented!("long long is also too long for rcc apparently"),
                _ => {
                    self.error_handler
                        .error(SemanticError::TooLong(long_count), location);
                    ctype = Some(Type::Long(signed));
                }
            }
        }
        let qualifiers = Qualifiers {
            c_const: counter.get(&Const).is_some(),
            volatile: counter.get(&Volatile).is_some(),
            func: FunctionQualifiers {
                inline: counter.get(&Inline).is_some(),
                no_return: counter.get(&NoReturn).is_some(),
            },
        };
        let mut storage_class = None;
        for (spec, sc) in &[
            (Auto, StorageClass::Auto),
            (Register, StorageClass::Register),
            (Static, StorageClass::Static),
            (Extern, StorageClass::Extern),
        ] {
            if counter.get(spec).is_some() {
                if let Some(existing) = storage_class {
                    self.error_handler.error(
                        SemanticError::ConflictingStorageClass(existing, *sc),
                        location,
                    );
                }
                storage_class = Some(*sc);
            }
        }
        // TODO: maybe use `iter!` macro instead of `vec!` to avoid an allocation?
        // https://play.rust-lang.org/?gist=0535aa4f749a14cb1b28d658446f3c13
        for (spec, new_ctype) in vec![
            (Bool, Type::Bool),
            (Char, Type::Char(signed)),
            (Short, Type::Short(signed)),
            (Int, Type::Int(signed)),
            // already handled `long` when we handled `long long`
            (Float, Type::Float),
            (Double, Type::Double),
            (Void, Type::Void),
            (VaList, Type::VaList),
        ] {
            if counter.get(&spec).is_some() {
                if let Some(existing) = ctype {
                    self.error_handler.error(
                        SemanticError::ConflictingType(existing, new_ctype.clone()),
                        location,
                    );
                }
                ctype = Some(new_ctype);
            }
        }
        for compound in compounds {
            match compound {
                Unit(_) => unreachable!("already caught"),
                Typedef => {
                    if let Some(existing) = storage_class {
                        self.error_handler.error(
                            SemanticError::ConflictingStorageClass(existing, StorageClass::Typedef),
                            location,
                        );
                    }
                    storage_class = Some(StorageClass::Typedef);
                }
                Enum { .. } | Struct(_) | Union(_) => unimplemented!("compound types"),
            }
        }
        // Check to see if we had a conflicting `signed` specifier
        // Note we use `counter` instead of the `signed` bool
        // because we've already set the default and forgotten whether it was originally present.
        if counter.get(&Signed).is_some() {
            match &ctype {
                // unsigned int
                Some(Type::Char(_)) | Some(Type::Short(_)) | Some(Type::Int(_))
                | Some(Type::Long(_)) => {}
                // unsigned float
                Some(other) => {
                    let err = SemanticError::CannotBeSigned(other.clone());
                    self.error_handler.error(err, location);
                }
                // unsigned i
                None => ctype = Some(Type::Int(signed)),
            }
        }
        // i;
        let ctype = ctype.unwrap_or_else(|| {
            self.error_handler.warn(Warning::ImplicitInt, location);
            Type::Int(true)
        });
        ParsedType {
            qualifiers,
            storage_class,
            ctype,
            // TODO: set this properly when I implement enum/struct/union
            declared_compound_type: false,
        }
    }
    /// Parse the declarator for a variable, given a starting type.
    /// e.g. for `int *p`, takes `start: Type::Int(true)` and returns `Type::Pointer(Type::Int(true))`
    fn parse_declarator(
        &mut self, current: Type, decl: ast::DeclaratorType, location: Location,
    ) -> Type {
        use crate::data::ast::DeclaratorType::*;
        use crate::data::types::ArrayType;
        match decl {
            End => current,
            Pointer { to, qualifiers } => {
                use UnitSpecifier::*;

                let inner = self.parse_declarator(current, *to, location);
                let (counter, compounds) =
                    count_specifiers(qualifiers, &mut self.error_handler, location);
                let qualifiers = Qualifiers {
                    c_const: counter.get(&Const).is_some(),
                    volatile: counter.get(&Volatile).is_some(),
                    func: FunctionQualifiers {
                        inline: counter.get(&Inline).is_some(),
                        no_return: counter.get(&NoReturn).is_some(),
                    },
                };
                for &q in counter.keys() {
                    if !q.is_qualifier() {
                        self.error_handler
                            .error(SemanticError::NotAQualifier(q.into()), location);
                    }
                }
                for spec in compounds {
                    self.error_handler
                        .error(SemanticError::NotAQualifier(spec), location);
                }
                Type::Pointer(Box::new(inner), qualifiers)
            }
            Array { of, size } => {
                let size = if let Some(expr) = size {
                    let size = Self::const_int(self.parse_expr(*expr)).unwrap_or_else(|err| {
                        self.error_handler.push_back(err);
                        1
                    });
                    ArrayType::Fixed(size)
                } else {
                    ArrayType::Unbounded
                };
                let of = self.parse_declarator(current, *of, location);
                Type::Array(Box::new(of), size)
            }
            Function(func) => unimplemented!(),
        }
    }
    // used for arrays like `int a[BUF_SIZE - 1];`
    fn const_int(expr: Expr) -> CompileResult<crate::arch::SIZE_T> {
        use Literal::*;

        let expr = expr.const_fold()?;
        let location = expr.location;
        let lit = expr.into_literal().or_else(|runtime_expr| {
            Err(Locatable::new(
                SemanticError::NotConstant(runtime_expr),
                location,
            ))
        })?;
        match lit {
            UnsignedInt(i) => Ok(i),
            Int(i) => {
                if i < 0 {
                    Err(Locatable::new(
                        SemanticError::NegativeLength.into(),
                        location,
                    ))
                } else {
                    Ok(i as u64)
                }
            }
            Char(c) => Ok(c.into()),
            Str(_) | Float(_) => Err(Locatable::new(
                SemanticError::NonIntegralLength.into(),
                location,
            )),
        }
    }
    fn parse_initializer(
        &mut self, init: ast::Initializer, ctype: &Type, location: Location,
    ) -> Initializer {
        unimplemented!("initializers")
    }
    fn parse_expr(&mut self, expr: ast::Expr) -> Expr {
        match expr {
            _ => unimplemented!(),
        }
    }
    /*
    fn parse_id(&mut self, name: InternedStr) {
        match self.scope.get(&name) {
            None => {
                self.error_handler.push_back(CompileError::new(
                    SemanticError::UndeclaredVar(name).into(),
                    location,
                ));
                Ok(pretend_zero)
            }
            Some(symbol) => {
                if symbol.storage_class == StorageClass::Typedef {
                    self.error_handler.push_back(
                        location.error(SemanticError::TypedefInExpressionContext),
                    );
                    return Ok(pretend_zero);
                }
                if let Type::Enum(ident, members) = &symbol.ctype {
                    let enumerator = members.iter().find_map(|(member, value)| {
                        if name == *member {
                            Some(*value)
                        } else {
                            None
                        }
                    });
                    if let Some(e) = enumerator {
                        return Ok(Expr {
                            constexpr: true,
                            ctype: Type::Enum(*ident, members.clone()),
                            location,
                            lval: false,
                            expr: ExprType::Literal(Literal::Int(e)),
                        });
                    }
                }
                Ok(Expr::id(symbol, location))
            }
    }
    */
}
struct FunctionAnalyzer<'a> {
    /// the function we are currently compiling.
    /// used for checking return types
    metadata: FunctionData,
    /// We need this for the scopes, as well as for parsing expressions
    analyzer: &'a mut Analyzer,
    /*
    /// objects that are in scope
    /// It's a reference instead of an owned scope since the global variables are passed in from the `Analyzer`.
    scope: &'a mut Scope<InternedStr, MetadataRef>,
    /// compound types that are in scope: structs, unions, and enums
    /// scope 2. from above
    tag_scope: &'a mut TagScope,
    /// used for recovering from semantic errors
    error_handler: &'a mut ErrorHandler,
    */
}

#[derive(Debug)]
/// used to keep track of function metadata
/// while doing semantic analysis
struct FunctionData {
    /// the name of the function
    id: InternedStr,
    /// where the function was declared
    location: Location,
    /// the return type of the function
    return_type: Type,
}

impl<'a> FunctionAnalyzer<'a> {
    /// Performs semantic analysis on the function and adds it to `METADATA_STORE`.
    /// Returns the analyzed statements.
    fn analyze(
        func: ast::FunctionDefinition, analyzer: &mut Analyzer, location: Location,
    ) -> (MetadataRef, Vec<Stmt>) {
        let return_type: ParsedType =
            analyzer.parse_type(func.specifiers, func.declarator.into(), location);
        /*
        let return_type = func
            .declarator
            .return_type
            .parse_type(func.specifiers, error_handler, location)
            .map_err(|err| location.with(err))?;
            */
        if return_type.qualifiers != Qualifiers::default() {
            analyzer.error_handler.warn(
                Warning::FunctionQualifiersIgnored(return_type.qualifiers),
                location,
            );
        }
        let metadata = FunctionData {
            location,
            id: func.id,
            return_type: return_type.ctype,
        };
        assert!(analyzer.scope.is_global());
        assert!(analyzer.tag_scope.is_global());
        let analyzer = FunctionAnalyzer { metadata, analyzer };
        unimplemented!("analyzing functions");
        //assert!(global_scope.is_global());
        //assert!(tag_scope.is_global());
    }
}

struct ParsedType {
    // needs to be option because the default varies greatly depending on the context
    storage_class: Option<StorageClass>,
    qualifiers: Qualifiers,
    ctype: Type,
    // TODO: this is fishy
    declared_compound_type: bool,
}

use ast::{DeclarationSpecifier, UnitSpecifier};

fn count_specifiers(
    specifiers: Vec<DeclarationSpecifier>, error_handler: &mut ErrorHandler, location: Location,
) -> (Counter<UnitSpecifier, usize>, Vec<DeclarationSpecifier>) {
    use DeclarationSpecifier::*;
    use UnitSpecifier::*;

    let mut counter = Counter::<_, usize>::new();
    let mut compounds = Vec::new();
    for spec in specifiers {
        match spec {
            Unit(u) => counter.update(std::iter::once(u)),
            _ => compounds.push(spec),
        }
    }
    for (&spec, &count) in counter.iter() {
        if spec != Long && count > 1 {
            error_handler.warn(Warning::DuplicateSpecifier(spec, count), location);
        }
    }
    (counter, compounds)
}

impl UnitSpecifier {
    fn is_qualifier(self) -> bool {
        use UnitSpecifier::*;
        match self {
            Const | Volatile | Restrict | Inline | NoReturn => true,
            _ => false,
        }
    }
}

/*
fn desugar(expr: ExprType) -> data::Expr {
    unimplemented!()
    /*
    match expr {
        ExprType::Assign(lval, rval, token) => {
            // lval += rval -> { tmp = &lval; *tmp = rval; }
        }
    }
    */
}
*/

/*
fn analyze(declaration: ExternalDeclaration) {

}
*/

#[cfg(test)]
pub(crate) mod test {
    use super::{Error, *};
    use crate::data::types::{ArrayType, FunctionType, StructType, Type::*};
    use crate::test::*;

    fn analyze<P, A, R, S, E>(input: &str, parse_func: P, analyze_func: A) -> CompileResult<R>
    where
        P: Fn(&mut Parser) -> Result<S, E>,
        A: Fn(&mut Analyzer, S) -> R,
        CompileError: From<E>,
    {
        let mut p = parser(input);
        let ast = parse_func(&mut p)?;
        if let Some(err) = p.error_handler.pop_front() {
            return Err(err);
        }
        let mut a = Analyzer::new(p);
        let e = analyze_func(&mut a, ast);
        if let Some(err) = a.error_handler.pop_front() {
            return Err(err);
        }
        Ok(e)
    }

    fn maybe_decl(s: &str) -> Option<CompileResult<Declaration>> {
        let mut parser = parser(s);
        if let Some(err) = parser.error_handler.pop_front() {
            return Some(Err(err));
        }
        Analyzer::new(parser).next().map(|o| o.map(|l| l.data))
    }

    pub(crate) fn decl(s: &str) -> CompileResult<Declaration> {
        maybe_decl(s).unwrap()
    }

    pub(crate) fn analyze_expr(s: &str) -> CompileResult<Expr> {
        analyze(s, Parser::expr, Analyzer::parse_expr)
    }

    fn assert_decl_display(left: &str, right: &str) {
        assert_eq!(decl(left).unwrap().to_string(), right);
    }

    fn match_type(lexed: CompileResult<Declaration>, given_type: Type) -> bool {
        lexed.map_or(false, |data| data.symbol.get().ctype == given_type)
    }

    #[test]
    fn no_name_should_be_syntax_error() {
        match decl("int *;").unwrap_err().data {
            Error::Syntax(_) => {}
            _ => panic!("expected syntax error"),
        }
    }

    #[test]
    fn storage_class() {
        assert_decl_display("int i;", "extern int i;");
        match decl("auto int i;").unwrap_err().data {
            Error::Semantic(SemanticError::AutoAtGlobalScope) => {}
            _ => panic!("wrong error"),
        }
    }
    #[test]
    fn test_decl_specifiers() {
        assert!(match_type(decl("char i;"), Type::Char(true)));
        assert!(match_type(decl("unsigned char i;"), Type::Char(false)));
        assert!(match_type(decl("signed short i;"), Type::Short(true)));
        assert!(match_type(decl("unsigned short i;"), Type::Short(false)));
        assert!(match_type(decl("long i;"), Type::Long(true)));
        assert!(match_type(decl("long long i;"), Type::Long(true)));
        assert!(match_type(decl("long unsigned i;"), Type::Long(false)));
        assert!(match_type(decl("int i;"), Type::Int(true)));
        assert!(match_type(decl("signed i;"), Type::Int(true)));
        assert!(match_type(decl("unsigned i;"), Type::Int(false)));
        assert!(match_type(decl("float f;"), Type::Float));
        assert!(match_type(decl("double d;"), Type::Double));
        assert!(match_type(decl("long double d;"), Type::Double));
        assert!(match_type(
            decl("void f();"),
            Type::Function(FunctionType {
                return_type: Box::new(Type::Void),
                params: vec![],
                varargs: false
            })
        ));
        assert!(match_type(decl("const volatile int f;"), Type::Int(true)));
    }
    #[test]
    fn test_bad_decl_specs() {
        assert!(maybe_decl("int;").is_none());
        for s in &[
            "char char i;",
            "char long i;",
            "long char i;",
            "float char i;",
            "float double i;",
            "double double i;",
            "double unsigned i;",
            "short double i;",
            "int void i;",
            "void int i;",
        ] {
            assert!(decl(s).is_err());
        }
        // default to int if we don't have a type
        // don't panic if we see duplicate specifiers
        assert!(match_type(decl("unsigned unsigned i;"), Type::Int(false)));
        assert!(match_type(decl("extern extern i;"), Type::Int(true)));
        assert!(match_type(decl("const const i;"), Type::Int(true)));
        assert!(match_type(decl("const volatile i;"), Type::Int(true)));
    }
    #[test]
    fn test_arrays() {
        assert!(match_type(
            decl("int a[];"),
            Array(Box::new(Int(true)), ArrayType::Unbounded)
        ));
        assert!(match_type(
            decl("unsigned a[];"),
            Array(Box::new(Int(false)), ArrayType::Unbounded)
        ));
        assert!(match_type(
            decl("_Bool a[][][];"),
            Array(
                Box::new(Array(
                    Box::new(Array(Box::new(Bool), ArrayType::Unbounded)),
                    ArrayType::Unbounded
                )),
                ArrayType::Unbounded
            )
        ));
    }
    /*
        #[test]
        fn test_pointers() {
            assert_no_change("void *a;"), Pointer(Box::new(Void))));
            assert!(match_type(
                decl("float *const a;"),
                Pointer(Box::new(Float))
            ));
            // cdecl: declare a as const pointer to volatile pointer to double
            assert!(match_type(
                decl("double *volatile *const a;"),
                Pointer(Box::new(Pointer(Box::new(Double))),)
            ));
            assert!(match_type(
                decl("_Bool *volatile const a;"),
                Pointer(Box::new(Bool)),
            ));
            assert!(match_type(
                decl("char (*(*f));"),
                Pointer(Box::new(Pointer(Box::new(Char(true)))))
            ));
        }
        #[test]
        fn test_pointers_and_arrays() {
            // cdecl: declare foo as array 10 of pointer to pointer to char
            assert!(match_type(
                decl("char **foo[10];"),
                Array(
                    Box::new(Pointer(Box::new(Pointer(Box::new(Char(true)))))),
                    ArrayType::Fixed(10),
                )
            ));
            // cdecl: declare foo as pointer to pointer to array 10 of int
            assert!(match_type(
                decl("int (**foo)[10];"),
                Pointer(Box::new(Pointer(Box::new(Array(
                    Box::new(Int(true)),
                    ArrayType::Fixed(10)
                )))),)
            ));
        }
        #[test]
        fn test_functions() {
            assert!(match_type(
                decl("void *f();"),
                Function(FunctionType {
                    return_type: Box::new(Pointer(Box::new(Type::Void))),
                    params: vec![],
                    varargs: false,
                })
            ));
            // cdecl: declare i as pointer to function returning int;
            assert!(match_type(
                decl("int (*i)();"),
                Pointer(Box::new(Function(FunctionType {
                    return_type: Box::new(Int(true)),
                    params: vec![],
                    varargs: false,
                })),)
            ));
            // cdecl: declare i as pointer to function (int, char, float) returning int
            assert!(match_type(
                decl("int (*i)(int, char, float);"),
                Pointer(Box::new(Function(FunctionType {
                    return_type: Box::new(Int(true)),
                    params: vec![
                        Symbol {
                            id: Default::default(),
                            ctype: Int(true),
                            qualifiers: Default::default(),
                            init: true,
                            storage_class: Default::default()
                        },
                        Symbol {
                            id: Default::default(),
                            ctype: Char(true),
                            qualifiers: Default::default(),
                            init: true,
                            storage_class: Default::default()
                        },
                        Symbol {
                            id: Default::default(),
                            ctype: Float,
                            qualifiers: Default::default(),
                            init: true,
                            storage_class: Default::default()
                        }
                    ],
                    varargs: false,
                })),)
            ));
                // cdecl: declare i as pointer to function (pointer to function returning int) returning int
                assert!(match_type(
                    decl("int (*i)(int (*f)());"),
                    Pointer(Box::new(Function(FunctionType {
                        return_type: Box::new(Int(true)),
                        params: vec![Symbol {
                            id: InternedStr::get_or_intern("f"),
                            ctype: Pointer(Box::new(Function(FunctionType {
                                return_type: Box::new(Int(true)),
                                params: vec![],
                                varargs: false
                            })),),
                            qualifiers: Default::default(),
                            storage_class: Default::default(),
                            init: true,
                        }],
                        varargs: false,
                    }),),)
                ));
                assert!(match_type(
                    decl("int f(int, ...);"),
                    Function(FunctionType {
                        return_type: Box::new(Int(true)),
                        params: vec![Symbol {
                            id: Default::default(),
                            ctype: Int(true),
                            qualifiers: Default::default(),
                            init: true,
                            storage_class: Default::default()
                        }],
                        varargs: true,
                    })
                ));
            }
            #[test]
            fn test_functions_array_parameter_static() {
                assert!(match_type(
                    decl("void f(int a[static 5]);"),
                    Function(FunctionType {
                        return_type: Box::new(Void),
                        params: vec![Symbol {
                            id: InternedStr::get_or_intern("a"),
                            ctype: Pointer(Box::new(Int(true))),
                            qualifiers: Default::default(),
                            storage_class: Default::default(),
                            init: true,
                        }],
                        varargs: false
                    })
                ));

                assert!(decl("int b[static 10];").unwrap().is_err());
            }
            #[test]
            fn test_inline_keyword() {
                // Correct usage
                assert!(match_type(
                    decl("inline void f(void);"),
                    Function(FunctionType {
                        return_type: Box::new(Void),
                        params: vec![],
                        varargs: false,
                    })
                ));

                // `inline` is not allowed in the following cases
                assert!(decl("inline int a;").unwrap().is_err()); // Normal declarations
                assert!(decl("void f(inline int a);").unwrap().is_err()); // Parameter lists
                assert!(decl("struct F { inline int a; } f;").unwrap().is_err()); // Struct members
                assert!(
                    decl("int main() { char a = (inline char)(4); }") // Type names
                    .unwrap()
                    .is_err()
            );
            assert!(decl("typedef a inline int;").unwrap().is_err());
        }
        #[test]
        fn test_complex() {
            // cdecl: declare bar as const pointer to array 10 of pointer to function (int) returning const pointer to char
            assert!(match_type(
                decl("char * const (*(* const bar)[])(int );"),
                Pointer(Box::new(Array(
                    Box::new(Pointer(Box::new(Function(FunctionType {
                        return_type: Box::new(Pointer(Box::new(Char(true)))),
                        params: vec![Symbol {
                            ctype: Int(true),
                            storage_class: Default::default(),
                            id: Default::default(),
                            qualifiers: Qualifiers::NONE,
                            init: true,
                        }],
                        varargs: false,
                    })),)),
                    ArrayType::Unbounded,
                )),)
            ));
            // cdecl: declare foo as pointer to function (void) returning pointer to array 3 of int
            assert!(match_type(
                decl("int (*(*foo)(void))[];"),
                Pointer(Box::new(Function(FunctionType {
                    return_type: Box::new(Pointer(Box::new(Array(
                        Box::new(Int(true)),
                        ArrayType::Unbounded
                    )),)),
                    params: vec![Symbol {
                        ctype: Void,
                        storage_class: Default::default(),
                        id: Default::default(),
                        qualifiers: Default::default(),
                        init: true,
                    }],
                    varargs: false,
                })),)
            ));
            // cdecl: declare bar as volatile pointer to array 64 of const int
            assert!(match_type(
                decl("const int (* volatile bar)[];"),
                Pointer(Box::new(Array(Box::new(Int(true)), ArrayType::Unbounded)),)
            ));
            // cdecl: declare x as function returning pointer to array 5 of pointer to function returning char
            assert!(match_type(
                decl("char (*(*x())[])();"),
                Function(FunctionType {
                    return_type: Box::new(Pointer(Box::new(Array(
                        Box::new(Pointer(Box::new(Function(FunctionType {
                            return_type: Box::new(Char(true)),
                            params: vec![],
                            varargs: false,
                        })),)),
                        ArrayType::Unbounded
                    )),)),
                    params: vec![],
                    varargs: false,
                })
            ));
        }
        #[test]
        fn test_multiple() {
            let parsed = parse_all("int i, j, k;");
            assert!(parsed.len() == 3);
            assert!(match_all(parsed.into_iter(), |i| i.symbol.ctype == Type::Int(true)))
            assert!(match_all(parsed.into_iter(), |i| i.symbol.ctype == Type::Int(true)));
            let mut parsed = parse_all("char *p, c, **pp, f();");
            assert!(parsed.len() == 4);
            assert!(match_type(
                Some(parsed.remove(0)),
                Type::Pointer(Box::new(Type::Char(true))),
            ));
            assert!(match_type(Some(parsed.remove(0)), Type::Char(true)));
            assert!(match_type(
                Some(parsed.remove(0)),
                Type::Pointer(Box::new(Type::Pointer(Box::new(Type::Char(true)),)),)
            ));
            assert!(match_type(
                Some(parsed.remove(0)),
                Type::Function(FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::Char(true)),
                    varargs: false,
                })
            ));
        }
        #[test]
        fn test_no_specifiers() {
            let parsed = parse_all("i, j, k;");
            assert!(parsed.len() == 3);
            assert!(match_all(parsed.into_iter(), |i| i.symbol.ctype == Type::Int(true)));
            let mut parsed = parse_all("*p, c, **pp, f();");
            assert!(parsed.len() == 4);
            assert!(match_type(
                Some(parsed.remove(0)),
                Type::Pointer(Box::new(Type::Int(true)))
            ));
            assert!(match_type(Some(parsed.remove(0)), Type::Int(true)));
            assert!(match_type(
                Some(parsed.remove(0)),
                Type::Pointer(Box::new(Type::Pointer(Box::new(Type::Int(true)))))
            ));
            assert!(match_type(
                Some(parsed.remove(0)),
                Type::Function(FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::Int(true)),
                    varargs: false,
                })
            ));
        }
        #[test]
        fn test_decl_errors() {
            // no semicolon
            assert!(decl("int").unwrap().is_err());
            assert!(decl("int i").unwrap().is_err());
            // type error: cannot have array of functions or function returning array
            assert!(decl("int f()[];").unwrap().is_err());
            assert!(decl("int f[]();").unwrap().is_err());
            assert!(decl("int f()();").unwrap().is_err());
            assert!(decl("int (*f)[;").unwrap().is_err());
            // duplicate parameter name
            assert!(decl("int f(int a, int a);").unwrap().is_err());
        }
        #[test]
        fn test_initializers() {
            // scalars
            assert!(decl("int i = 3;").unwrap().is_ok());

            // bounded and unbounded arrays
            let parsed = [
                decl("int a[] = {1, 2, 3};"),
                decl("int a[3] = {1, 2, 3};"),
                // possibly with trailing commas
                decl("int a[] = {1, 2, 3,};"),
                decl("int a[3] = {1, 2, 3,};"),
                // or nested
                decl("int a[][3] = {{1, 2, 3}};"),
                decl("int a[][3] = {{1, 2, 3,}};"),
                decl("int a[][3] = {{1, 2, 3,},};"),
                decl("int a[1][3] = {{1, 2, 3,},};"),
                // with misleading braces
                decl("int a[][3] = {1, 2, 3};"),
                decl("int a[][3] = {1, 2, 3,};"),
            ];
            for res in &parsed {
                match res.as_ref().unwrap() {
                    Ok(Locatable {
                        data:
                            Declaration {
                                init: Some(Initializer::InitializerList(_)),
                                ..
                            },
                        ..
                    }) => {}
                    Ok(Locatable { data, .. }) => {
                        panic!("expected initializer list, got declaration: {}", data)
                    }
                    Err(Locatable { data, .. }) => {
                        panic!("expected initializer list, got error: {}", data)
                    }
                };
            }
            for err in &["int i = {};", "int a[] = {};", "int a[][3] = {{}};"] {
                assert!(decl(err).unwrap().is_err());
            }
        }

        #[test]
        fn default_type_specifier_warns() {
            let default_type_decls = &[
                "i;",
                "f();",
                "a[1];",
                "(*fp)();",
                "(i);",
                "((*f)());",
                "(a[1]);",
                "(((((((((i)))))))));",
            ];

            for decl in default_type_decls {
                assert_errs_decls(decl, 0, 1, 1);
            }
        }

        #[test]
        fn extern_redeclaration_of_static_fn_does_not_error() {
            let code = "
                static int f();
                extern int f();
            ";

            assert_errs_decls(code, 0, 0, 2);

            // However the opposite should still error
            let code = "
                extern int f();
                static int f();
            ";

            assert_errs_decls(code, 1, 0, 2);
        }

        #[test]
        fn enum_declaration() {
            assert!(decl("enum;").unwrap().is_err());
            assert!(decl("enum e;").unwrap().is_err());
            assert!(decl("enum e {};").unwrap().is_err());
            assert!(decl("enum e { A }").unwrap().is_err());
            assert!(decl("enum { A };").is_none());
            assert!(match_type(
                decl("enum { A } E;"),
                Type::Enum(None, vec![("A".into(), 0)])
            ));
            assert!(match_type(
                decl("enum e { A = 1, B } E;"),
                Type::Enum(Some("e".into()), vec![("A".into(), 1), ("B".into(), 2)])
            ));
            assert!(match_type(
                decl("enum { A = -5, B, C = 2, D } E;"),
                Type::Enum(
                    None,
                    vec![
                        ("A".into(), -5),
                        ("B".into(), -4),
                        ("C".into(), 2),
                        ("D".into(), 3)
                    ]
                )
            ));
        }
        #[test]
        fn typedef_signed() {
            let mut parsed = parse_all("typedef unsigned uint; uint i;");
            assert!(match_type(parsed.pop(), Type::Int(false)));
        }
        #[test]
        fn bitfields() {
            assert!(decl("struct { int:5; } a;").unwrap().is_err());
            assert!(decl("struct { int a:5; } b;").unwrap().is_ok());
            assert!(decl("struct { int a:5, b:6; } c;").unwrap().is_ok());
            assert!(decl("struct { extern int a:5; } d;").unwrap().is_err());
        }
        #[test]
        fn lol() {
            let lol = "
    int *jynelson(int(*fp)(int)) {
        return 0;
    }
    int f(int i) {
        return 0;
    }
    int main() {
        return *((int*(*)(int(*)(int)))jynelson)(&f);
    }
    ";
            assert!(parse_all(lol).iter().all(Result::is_ok));
        }
        */
}
