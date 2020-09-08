mod expr;
mod init;
mod stmt;

use std::collections::{HashSet, VecDeque};
use std::convert::TryInto;

use counter::Counter;

use crate::data::{error::Warning, hir::*, lex::Keyword, *};
use crate::intern::InternedStr;
use crate::parse::{Lexer, Parser};
use crate::RecursionGuard;

pub(crate) type TagScope = Scope<InternedStr, TagEntry>;

#[derive(Clone, Debug)]
pub(crate) enum TagEntry {
    Struct(StructRef),
    Union(StructRef),
    // list of (name, value)s
    Enum(Vec<(InternedStr, i64)>),
}

/// The driver for `PureAnalyzer`.
///
/// This implements `Iterator` and ensures that declarations and errors are returned in the correct error.
/// Use this if you want to compile an entire C program,
/// or if it is important to show errors in the correct order relative to declarations.
pub struct Analyzer<T: Lexer> {
    declarations: Parser<T>,
    pub inner: PureAnalyzer,
    /// Whether to print each declaration as it is seen
    pub debug: bool,
}

/// A `PureAnalyzer` turns AST types into HIR types.
///
/// In particular, it performs type checking and semantic analysis.
/// Use this if you need to analyze a specific AST data type without parsing a whole program.

// The struct is used mostly for holding scopes and error handler.
pub struct PureAnalyzer {
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
    scope: Scope<InternedStr, Symbol>,
    /// the compound types that have been declared (struct/union/enum)
    /// scope 2. from above
    tag_scope: TagScope,
    /// Stores all variables that have been initialized so far
    initialized: HashSet<Symbol>,
    /// Internal API which makes it easier to return errors lazily
    error_handler: ErrorHandler,
    /// Internal API which prevents segfaults due to stack overflow
    recursion_guard: RecursionGuard,
    /// Hack to make compound assignment work
    ///
    /// For `a += b`, `a` must only be evaluated once.
    /// The way `assignment_expr` handles this is by desugaring to
    /// `tmp = &a; *tmp = *tmp + b;`
    /// However, the backend still has to see the declaration.
    /// There's no way to return a statement from an expression,
    /// so instead we store it in a side channel.
    ///
    /// TODO: this should be a field on `FunctionAnalyzer`, not `Analyzer`
    decl_side_channel: Vec<Locatable<Declaration>>,
}

impl<T: Lexer> Iterator for Analyzer<T> {
    type Item = CompileResult<Locatable<Declaration>>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // Instead of returning `SemanticResult`, the analyzer puts all errors into `error_handler`.
            // This simplifies the logic in `next` greatly.
            // NOTE: this returns errors for a declaration before the declaration itself
            if let Some(err) = self.inner.error_handler.pop_front() {
                return Some(Err(err));
            // If we saw `int i, j, k;`, we treated those as different declarations
            // `j, k` will be stored into `pending`
            } else if let Some(decl) = self.inner.pending.pop_front() {
                if self.debug {
                    println!("hir: {}", decl.data);
                }
                return Some(Ok(decl));
            }
            // Now do the real work.
            let next = match self.declarations.next()? {
                Err(err) => return Some(Err(err)),
                Ok(decl) => decl,
            };
            let decls = self.inner.parse_external_declaration(next);
            // TODO: if an error occurs, should we still add the declaration to `pending`?
            self.inner.pending.extend(decls);
        }
    }
}

impl<I: Lexer> Analyzer<I> {
    pub fn new(parser: Parser<I>, debug: bool) -> Self {
        Self {
            declarations: parser,
            debug,
            inner: PureAnalyzer::new(),
        }
    }
}

impl Default for PureAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl PureAnalyzer {
    pub fn new() -> Self {
        Self {
            error_handler: ErrorHandler::new(),
            scope: Scope::new(),
            tag_scope: Scope::new(),
            pending: VecDeque::new(),
            initialized: HashSet::new(),
            recursion_guard: RecursionGuard::default(),
            decl_side_channel: Vec::new(),
        }
    }

    /// Return all warnings seen so far.
    ///
    /// These warnings are consumed and will not be returned if you call
    /// `warnings()` again.
    pub fn warnings(&mut self) -> VecDeque<CompileWarning> {
        std::mem::take(&mut self.error_handler.warnings)
    }

    /// Return all errors seen so far.
    ///
    /// These errors are consumed and will not be returned if you call
    /// `errors()` again.
    pub fn errors(&mut self) -> VecDeque<Locatable<Error>> {
        std::mem::take(&mut self.error_handler.errors)
    }

    // I type these a lot
    #[inline(always)]
    fn err(&mut self, e: SemanticError, l: Location) {
        self.error_handler.error(e, l);
    }
    #[inline(always)]
    fn warn(&mut self, w: Warning, l: Location) {
        self.error_handler.warn(w, l);
    }
    fn recursion_check(&mut self) -> RecursionGuard {
        self.recursion_guard
            .recursion_check(&mut self.error_handler)
    }
    /// 6.9 External Definitions
    ///
    /// Either a function or a list of declarations.
    fn parse_external_declaration(
        &mut self,
        next: Locatable<ast::ExternalDeclaration>,
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
                self.parse_declaration(declaration, next.location)
            }
        }
    }
    /// A list of declarations: `int i, j, k;`
    fn parse_declaration(
        &mut self,
        declaration: ast::Declaration,
        location: Location,
    ) -> Vec<Locatable<Declaration>> {
        let original = self.parse_specifiers(declaration.specifiers, location);

        if original.storage_class == Some(StorageClass::Auto) && self.scope.is_global() {
            self.err(SemanticError::AutoAtGlobalScope, location);
        }

        // TODO: this is such a hack: https://github.com/jyn514/rcc/issues/371
        let sc = original.storage_class.unwrap_or(StorageClass::Auto);
        let mut decls = Vec::new();
        for d in declaration.declarators {
            let mut ctype =
                self.parse_declarator(original.ctype.clone(), d.data.declarator.decl, d.location);

            if !ctype.is_function() && original.qualifiers.func != FunctionQualifiers::default() {
                self.err(
                    SemanticError::FuncQualifiersNotAllowed(original.qualifiers.func),
                    d.location,
                );
            }

            let id = d.data.declarator.id;
            let id = match id {
                Some(i) => i,
                // int i, ();
                None => {
                    self.err("declarations cannot be abstract".into(), d.location);
                    "<error>".into()
                }
            };
            // NOTE: the parser handles typedefs on its own
            if ctype == Type::Void && sc != StorageClass::Typedef {
                // TODO: catch this error for types besides void?
                self.err(SemanticError::VoidType, location);
                ctype = Type::Error;
            }
            let init = if let Some(init) = d.data.init {
                Some(self.parse_initializer(init, &ctype, d.location))
            } else {
                None
            };
            let symbol = Variable {
                ctype,
                id,
                qualifiers: original.qualifiers,
                storage_class: sc,
            };
            let symbol = self.declare(symbol, init.is_some(), d.location);
            if init.is_some() {
                self.initialized.insert(symbol);
            }
            decls.push(Locatable::new(Declaration { symbol, init }, d.location));
        }
        // int;
        if decls.is_empty() && !original.declared_compound_type {
            self.warn(Warning::EmptyDeclaration, location);
        }
        decls
    }
    #[cfg(test)]
    #[inline(always)]
    // used only for testing, so that I can keep `parse_typename` private most of the time
    pub(crate) fn parse_typename_test(&mut self, ctype: ast::TypeName, location: Location) -> Type {
        self.parse_typename(ctype, location)
    }
    /// Perform checks for parsing a single type name.
    ///
    /// Type names are used most often in casts: `(int)i`
    /// This allows `int` or `int *` or `int (*)()`, but not `int i, j;` or `int i`
    ///
    /// 6.7.7 Type names
    fn parse_typename(&mut self, ctype: ast::TypeName, location: Location) -> Type {
        let parsed = self.parse_type(ctype.specifiers, ctype.declarator.decl, location);
        // TODO: should these be syntax errors instead?
        // extern int
        if let Some(sc) = parsed.storage_class {
            self.err(SemanticError::IllegalStorageClass(sc), location);
        }
        // const int
        if parsed.qualifiers != Qualifiers::default() {
            self.warn(Warning::IgnoredQualifier(parsed.qualifiers), location);
        }
        // int i
        if let Some(id) = ctype.declarator.id {
            self.err(SemanticError::IdInTypeName(id), location);
        }
        parsed.ctype
    }
    /// Parse a single type, given the specifiers and declarator.
    fn parse_type(
        &mut self,
        specifiers: Vec<ast::DeclarationSpecifier>,
        declarator: ast::DeclaratorType,
        location: Location,
    ) -> ParsedType {
        let mut specs = self.parse_specifiers(specifiers, location);
        specs.ctype = self.parse_declarator(specs.ctype, declarator, location);

        if !specs.ctype.is_function() && specs.qualifiers.func != FunctionQualifiers::default() {
            self.err(
                SemanticError::FuncQualifiersNotAllowed(specs.qualifiers.func),
                location,
            );
        }

        specs
    }
    /// The specifiers for a declaration: `const extern long int`
    ///
    /// Note that specifiers are also used for declaring structs, such as
    /// ```c
    /// struct s { int i; };
    /// ```
    /// Normally, we warn when a declaration is empty,
    /// but if we declared a struct, union, or enum, then no warning is emitted.
    /// This is kept track of by `declared_compound_type`.
    fn parse_specifiers(
        &mut self,
        specifiers: Vec<ast::DeclarationSpecifier>,
        location: Location,
    ) -> ParsedType {
        use ast::{DeclarationSpecifier::*, UnitSpecifier::*};

        // need to parse specifiers now
        // it's not enough to collect into a `Set` since `long long` has a different meaning than `long`
        // instead, we see how many times each specifier is present
        // however, for some specifiers this doesn't really make sense:
        // if we see `struct s { int i; }` twice in a row,
        // it's more likely that the user forgot a semicolon in between than tried to make some weird double struct type.
        // so: count the specifiers that are keywords and store the rest somewhere out of the way

        // 6.7.2 Type specifiers
        let (counter, compounds) = count_specifiers(specifiers, &mut self.error_handler, location);
        // Now that we've separated this into unit specifiers and compound specifiers,
        // see if we can pick up the proper types and qualifiers.
        let signed = match (counter.get(&Signed), counter.get(&Unsigned)) {
            // `int i` or `signed i`
            (None, None) | (Some(_), None) => true,
            // `unsigned i`
            (None, Some(_)) => false,
            // `unsigned signed i`
            (Some(_), Some(_)) => {
                self.err(SemanticError::ConflictingSigned, location);
                true
            }
        };
        // `long` is special because of `long long` and `long double`
        let mut ctype = None;
        if let Some(&long_count) = counter.get(&Long) {
            match long_count {
                0 => panic!("constraint violation, should only set count if > 0"),
                1 => {
                    // NOTE: this is handled later by the big `for type in [...]` loop
                    // see notes there
                    if counter.get(&Double).is_none() {
                        ctype = Some(Type::Long(signed));
                    }
                }
                // TODO: implement `long long` as a separate type
                2 => ctype = Some(Type::Long(signed)),
                _ => {
                    self.err(SemanticError::TooLong(long_count), location);
                    ctype = Some(Type::Long(signed));
                }
            }
        }
        // 6.7.3 Type qualifiers
        let qualifiers = Qualifiers {
            c_const: counter.get(&Const).is_some(),
            volatile: counter.get(&Volatile).is_some(),
            func: FunctionQualifiers {
                inline: counter.get(&Inline).is_some(),
                no_return: counter.get(&NoReturn).is_some(),
            },
        };
        // 6.7.1 Storage-class specifiers
        let mut storage_class = None;
        for (spec, sc) in &[
            (Auto, StorageClass::Auto),
            (Register, StorageClass::Register),
            (Static, StorageClass::Static),
            (Extern, StorageClass::Extern),
            (UnitSpecifier::Typedef, StorageClass::Typedef),
        ] {
            if counter.get(spec).is_some() {
                if let Some(existing) = storage_class {
                    self.err(
                        SemanticError::ConflictingStorageClass(existing, *sc),
                        location,
                    );
                }
                storage_class = Some(*sc);
            }
        }
        // back to type specifiers
        // TODO: maybe use `iter!` macro instead of `vec!` to avoid an allocation?
        // https://play.rust-lang.org/?gist=0535aa4f749a14cb1b28d658446f3c13
        for (spec, new_ctype) in vec![
            (Bool, Type::Bool),
            (Char, Type::Char(signed)),
            (Short, Type::Short(signed)),
            // already handled `long` when we handled `long long`
            (Float, Type::Float),
            // NOTE: if we saw `long double` before, we'll set `ctype` to `double` now
            // TODO: make `long double` different from `double`
            (Double, Type::Double),
            (Void, Type::Void),
            (VaList, Type::VaList),
        ] {
            if counter.get(&spec).is_some() {
                match (spec, ctype) {
                    // `short int` and `long int` are valid, see 6.7.2
                    // `long` is handled earlier, so we don't have to worry
                    // about it here.
                    (_, None) | (Short, Some(Type::Int(_))) => {}
                    (_, Some(existing)) => {
                        self.err(
                            SemanticError::ConflictingType(existing, new_ctype.clone()),
                            location,
                        );
                    }
                }
                ctype = Some(new_ctype);
            }
        }
        if counter.get(&Int).is_some() {
            match ctype {
                None => ctype = Some(Type::Int(signed)),
                // `long int` is valid
                Some(Type::Short(_)) | Some(Type::Long(_)) => {}
                Some(existing) => {
                    self.err(
                        SemanticError::ConflictingType(existing, Type::Int(signed)),
                        location,
                    );
                    ctype = Some(Type::Int(signed));
                }
            }
        }
        let mut declared_compound_type = false;
        for compound in compounds {
            let parsed = match compound {
                Unit(_) => unreachable!("already caught"),
                DeclarationSpecifier::Typedef(name) => {
                    let meta = self
                        .scope
                        .get(&name)
                        .expect("scope of parser and analyzer should match")
                        .get();
                    assert_eq!(meta.storage_class, StorageClass::Typedef);
                    meta.ctype.clone()
                }
                Struct(s) => self.struct_specifier(s, true, &mut declared_compound_type, location),
                Union(s) => self.struct_specifier(s, false, &mut declared_compound_type, location),
                Enum { name, members } => {
                    self.enum_specifier(name, members, &mut declared_compound_type, location)
                }
            };
            // TODO: this should report the name of the typedef, not the type itself
            if let Some(existing) = &ctype {
                self.err(
                    SemanticError::ConflictingType(existing.clone(), parsed.clone()),
                    location,
                );
            }
            ctype = Some(parsed);
        }
        // Check to see if we had a conflicting `signed` specifier
        // Note we use `counter` instead of the `signed` bool
        // because we've already set the default and forgotten whether it was originally present.
        if counter.get(&Signed).is_some() || counter.get(&Unsigned).is_some() {
            match &ctype {
                // unsigned int
                Some(Type::Char(_)) | Some(Type::Short(_)) | Some(Type::Int(_))
                | Some(Type::Long(_)) => {}
                // unsigned float
                Some(other) => {
                    let err = SemanticError::CannotBeSigned(other.clone());
                    self.err(err, location);
                }
                // unsigned i
                None => ctype = Some(Type::Int(signed)),
            }
        }
        // `i;` or `const i;`, etc.
        let ctype = ctype.unwrap_or_else(|| {
            self.warn(Warning::ImplicitInt, location);
            Type::Int(true)
        });
        ParsedType {
            qualifiers,
            storage_class,
            ctype,
            declared_compound_type,
        }
    }
    // 6.7.2.1 Structure and union specifiers
    fn struct_specifier(
        &mut self,
        struct_spec: ast::StructSpecifier,
        is_struct: bool,
        declared_struct: &mut bool,
        location: Location,
    ) -> Type {
        let ast_members = match struct_spec.members {
            // struct { int i; }
            Some(members) => members,
            // struct s
            None => {
                let name = if let Some(name) = struct_spec.name {
                    name
                } else {
                    // struct;
                    let err = format!(
                        "bare '{}' as type specifier is not allowed",
                        if is_struct { "struct" } else { "union " }
                    );
                    self.error_handler.error(SemanticError::from(err), location);
                    return Type::Error;
                };
                let keyword = if is_struct {
                    Keyword::Struct
                } else {
                    Keyword::Union
                };

                return match (is_struct, self.tag_scope.get(&name)) {
                    // `struct s *p;`
                    (_, None) => self.forward_declaration(keyword, name, location),
                    // `struct s; struct s;` or `struct s { int i; }; struct s`
                    (true, Some(TagEntry::Struct(s))) => Type::Struct(StructType::Named(name, *s)),
                    // `union s; union s;` or `union s { int i; }; union s`
                    (false, Some(TagEntry::Union(s))) => Type::Union(StructType::Named(name, *s)),
                    (_, Some(_)) => {
                        // `union s; struct s;`
                        if self.tag_scope.get_immediate(&name).is_some() {
                            let kind = if is_struct { "struct" } else { "union " };
                            // TODO: say what the previous declaration was
                            let err = SemanticError::from(format!("use of '{}' with type tag '{}' that does not match previous struct declaration", name, kind));
                            self.error_handler.push_back(Locatable::new(err, location));
                            Type::Error
                        } else {
                            // `union s; { struct s; }`
                            self.forward_declaration(keyword, name, location)
                        }
                    }
                };
            }
        };
        let members: Vec<_> = ast_members
            .into_iter()
            .map(|m| self.struct_declarator_list(m, location).into_iter())
            .flatten()
            .collect();
        if members.is_empty() {
            self.err(SemanticError::from("cannot have empty struct"), location);
            return Type::Error;
        }
        let constructor = if is_struct { Type::Struct } else { Type::Union };
        if let Some(id) = struct_spec.name {
            let struct_ref = if let Some(TagEntry::Struct(struct_ref))
            | Some(TagEntry::Union(struct_ref)) =
                self.tag_scope.get_immediate(&id)
            {
                let struct_ref = *struct_ref;
                // struct s { int i; }; struct s { int i; };
                if !struct_ref.get().is_empty() {
                    self.err(
                        SemanticError::from(format!(
                            "redefinition of {} '{}'",
                            if is_struct { "struct" } else { "union" },
                            id
                        )),
                        location,
                    );
                }
                struct_ref
            } else {
                StructRef::new()
            };
            struct_ref.update(members);
            let entry = if is_struct {
                TagEntry::Struct
            } else {
                TagEntry::Union
            }(struct_ref);
            self.tag_scope.insert(id, entry);
            *declared_struct = true;
            constructor(StructType::Named(id, struct_ref))
        } else {
            // struct { int i; }
            constructor(StructType::Anonymous(std::rc::Rc::new(members)))
        }
    }
    /*
    struct_declarator_list: struct_declarator (',' struct_declarator)* ;
    struct_declarator
        : declarator
        | ':' constant_expr  // bitfield, not supported
        | declarator ':' constant_expr
        ;
    */
    fn struct_declarator_list(
        &mut self,
        members: ast::StructDeclarationList,
        location: Location,
    ) -> Vec<Variable> {
        let parsed_type = self.parse_specifiers(members.specifiers, location);
        if parsed_type.qualifiers.has_func_qualifiers() {
            self.err(
                SemanticError::FuncQualifiersNotAllowed(parsed_type.qualifiers.func),
                location,
            );
        }

        let mut parsed_members = Vec::new();
        // A member of a structure or union may have any complete object type other than a variably modified type.
        for ast::StructDeclarator { decl, bitfield } in members.declarators {
            let decl = match decl {
                // 12 A bit-field declaration with no declarator, but only a colon and a width, indicates an unnamed bit-field.
                // TODO: this should give an error if `bitfield` is None.
                None => continue,
                Some(d) => d,
            };
            let ctype = match self.parse_declarator(parsed_type.ctype.clone(), decl.decl, location)
            {
                Type::Void => {
                    // TODO: catch this error for types besides void?
                    self.err(SemanticError::VoidType, location);
                    Type::Error
                }
                other => other,
            };
            let mut symbol = Variable {
                storage_class: StorageClass::Auto,
                qualifiers: parsed_type.qualifiers,
                ctype,
                id: decl.id.expect("struct members should have an id"),
            };
            // struct s { int i: 5 };
            if let Some(bitfield) = bitfield {
                let bit_size = match Self::const_uint(self.expr(bitfield)) {
                    Ok(e) => e,
                    Err(err) => {
                        self.error_handler.push_back(err);
                        1
                    }
                };
                let type_size = symbol.ctype.sizeof().unwrap_or(0);
                if bit_size == 0 {
                    let err = SemanticError::from(format!(
                        "C does not have zero-sized types. hint: omit the declarator {}",
                        symbol.id
                    ));
                    self.err(err, location);
                // struct s { int i: 65 }
                } else if bit_size > type_size * u64::from(crate::arch::CHAR_BIT) {
                    let err = SemanticError::from(format!(
                        "cannot have bitfield {} with size {} larger than containing type {}",
                        symbol.id, bit_size, symbol.ctype
                    ));
                    self.err(err, location);
                }
                self.error_handler.warn(
                    "bitfields are not implemented and will be ignored",
                    location,
                );
            }
            match symbol.ctype {
                Type::Struct(StructType::Named(_, inner_members))
                | Type::Union(StructType::Named(_, inner_members))
                    if inner_members.get().is_empty() =>
                {
                    self.err(
                        SemanticError::from(format!(
                            "cannot use type '{}' before it has been defined",
                            symbol.ctype
                        )),
                        location,
                    );
                    // add this as a member anyway because
                    // later code depends on structs being non-empty
                    symbol.ctype = Type::Error;
                }
                _ => {}
            }
            parsed_members.push(symbol);
        }
        // struct s { extern int i; };
        if let Some(class) = parsed_type.storage_class {
            let member = parsed_members
                .last()
                .expect("should have seen at least one declaration");
            self.err(
                SemanticError::from(format!(
                    "cannot specify storage class '{}' for struct member '{}'",
                    class, member.id,
                )),
                location,
            );
        }
        parsed_members
    }
    // 6.7.2.2 Enumeration specifiers
    fn enum_specifier(
        &mut self,
        enum_name: Option<InternedStr>,
        ast_members: Option<Vec<(InternedStr, Option<ast::Expr>)>>,
        saw_enum: &mut bool,
        location: Location,
    ) -> Type {
        *saw_enum = true;
        let ast_members = match ast_members {
            Some(members) => members,
            None => {
                // enum e
                let name = if let Some(name) = enum_name {
                    name
                } else {
                    // enum;
                    let err = SemanticError::from("bare 'enum' as type specifier is not allowed");
                    self.error_handler.error(err, location);
                    return Type::Error;
                };
                match self.tag_scope.get(&name) {
                    // enum e { A }; enum e my_e;
                    Some(TagEntry::Enum(members)) => {
                        *saw_enum = false;
                        return Type::Enum(Some(name), members.clone());
                    }
                    // struct e; enum e my_e;
                    Some(_) => {
                        // TODO: say what the previous type was
                        let err = SemanticError::from(format!("use of '{}' with type tag 'enum' that does not match previous struct declaration", name));
                        self.error_handler.push_back(Locatable::new(err, location));
                        return Type::Error;
                    }
                    // `enum e;` (invalid)
                    None => return self.forward_declaration(Keyword::Enum, name, location),
                }
            }
        };

        let mut discriminant = 0;
        let mut members = vec![];
        for (name, maybe_value) in ast_members {
            // enum E { A = 5 };
            if let Some(value) = maybe_value {
                discriminant = Self::const_sint(self.expr(value)).unwrap_or_else(|err| {
                    self.error_handler.push_back(err);
                    std::i64::MIN
                });
            }
            members.push((name, discriminant));
            // TODO: this is such a hack
            let tmp_symbol = Variable {
                id: name,
                qualifiers: Qualifiers {
                    c_const: true,
                    ..Default::default()
                },
                storage_class: StorageClass::Register,
                ctype: Type::Enum(None, vec![(name, discriminant)]),
            };
            self.declare(tmp_symbol, false, location);
            discriminant = discriminant.checked_add(1).unwrap_or_else(|| {
                self.error_handler
                    .push_back(location.error(SemanticError::EnumOverflow));
                0
            });
        }
        for (name, _) in &members {
            self.scope._remove(name);
        }
        // enum e {}
        if members.is_empty() {
            self.err(SemanticError::from("enums cannot be empty"), location)
        }
        if let Some(id) = enum_name {
            // enum e { A }; enum e { A };
            if self
                .tag_scope
                .insert(id, TagEntry::Enum(members.clone()))
                .is_some()
            {
                self.err(format!("redefition of enum '{}'", id).into(), location);
            }
        }
        let ctype = Type::Enum(enum_name, members);
        match &ctype {
            Type::Enum(_, members) => {
                for &(id, _) in members {
                    self.scope.insert(
                        id,
                        Variable {
                            id,
                            storage_class: StorageClass::Register,
                            qualifiers: Qualifiers::NONE,
                            ctype: ctype.clone(),
                        }
                        .insert(),
                    );
                }
            }
            _ => unreachable!(),
        }
        ctype
    }
    /// Used for forward declaration of structs and unions.
    ///
    /// Does not correspond to any grammar type.
    /// e.g. `struct s;`
    ///
    /// See also 6.7.2.3 Tags:
    /// > A declaration of the form `struct-or-union identifier ;`
    /// > specifies a structure or union type and declares the identifier as a tag of that type.
    /// > If a type specifier of the form `struct-or-union identifier`
    /// > occurs other than as part of one of the above forms, and no other declaration of the identifier as a tag is visible,
    /// > then it declares an incomplete structure or union type, and declares the identifier as the tag of that type.
    fn forward_declaration(
        &mut self,
        kind: Keyword,
        ident: InternedStr,
        location: Location,
    ) -> Type {
        if kind == Keyword::Enum {
            // see section 6.7.2.3 of the C11 standard
            self.err(
                SemanticError::from(format!(
                    "cannot have forward reference to enum type '{}'",
                    ident
                )),
                location,
            );
            return Type::Enum(Some(ident), vec![]);
        }
        let struct_ref = StructRef::new();
        let (entry_type, tag_type): (fn(_) -> _, fn(_) -> _) = if kind == Keyword::Struct {
            (TagEntry::Struct, Type::Struct)
        } else {
            (TagEntry::Union, Type::Union)
        };
        let entry = entry_type(struct_ref);
        self.tag_scope.insert(ident, entry);
        tag_type(StructType::Named(ident, struct_ref))
    }
    /// Parse the declarator for a variable, given a starting type.
    /// e.g. for `int *p`, takes `start: Type::Int(true)` and returns `Type::Pointer(Type::Int(true))`
    ///
    /// The parser generated a linked list `DeclaratorType`,
    /// which we now transform into the recursive `Type`.
    ///
    /// 6.7.6 Declarators
    fn parse_declarator(
        &mut self,
        current: Type,
        decl: ast::DeclaratorType,
        location: Location,
    ) -> Type {
        use crate::data::ast::DeclaratorType::*;
        use crate::data::types::{ArrayType, FunctionType};

        let _guard = self.recursion_check();
        match decl {
            End => current,
            Pointer { to, qualifiers } => {
                use UnitSpecifier::*;

                let inner = self.parse_declarator(current, *to, location);
                // we reuse `count_specifiers` even though we really only want the qualifiers
                let (counter, compounds) =
                    count_specifiers(qualifiers, &mut self.error_handler, location);
                // *const volatile
                // TODO: this shouldn't allow `inline` or `_Noreturn`
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
                        // *extern
                        self.err(SemanticError::NotAQualifier(q.into()), location);
                    }
                }
                for spec in compounds {
                    // *struct s {}
                    self.err(SemanticError::NotAQualifier(spec), location);
                }
                Type::Pointer(Box::new(inner), qualifiers)
            }
            Array { of, size } => {
                // int a[5]
                let size = if let Some(expr) = size {
                    let size = Self::const_uint(self.expr(*expr)).unwrap_or_else(|err| {
                        self.error_handler.push_back(err);
                        1
                    });
                    ArrayType::Fixed(size)
                } else {
                    // int a[]
                    ArrayType::Unbounded
                };
                let of = self.parse_declarator(current, *of, location);
                // int a[]()
                if let Type::Function(_) = &of {
                    self.err(SemanticError::ArrayStoringFunction(of.clone()), location);
                }
                Type::Array(Box::new(of), size)
            }
            Function(func) => {
                // TODO: give a warning for `const int f();` somewhere
                let return_type = self.parse_declarator(current, *func.return_type, location);
                match &return_type {
                    // int a()[]
                    Type::Array(_, _) => self.err(
                        SemanticError::IllegalReturnType(return_type.clone()),
                        location,
                    ),
                    // int a()()
                    Type::Function(_) => self.err(
                        SemanticError::IllegalReturnType(return_type.clone()),
                        location,
                    ),
                    _ => {}
                }

                let mut names = HashSet::new();
                let mut params = Vec::new();
                for param in func.params {
                    // TODO: this location should be that of the param, not of the function
                    let mut param_type =
                        self.parse_type(param.specifiers, param.declarator.decl, location);

                    // `int f(int a[])` -> `int f(int *a)`
                    if let Type::Array(to, _) = param_type.ctype {
                        param_type.ctype = Type::Pointer(to, Qualifiers::default());
                    }

                    // C11 Standard 6.7.6.3 paragraph 8
                    // "A declaration of a parameter as 'function returning type' shall be
                    //  adjusted to 'pointer to function returning type', as in 6.3.2.1."
                    // `int f(int g())` -> `int f(int (*g)())`
                    if param_type.ctype.is_function() {
                        param_type.ctype =
                            Type::Pointer(Box::new(param_type.ctype), Qualifiers::default());
                    }

                    // int a(extern int i)
                    if let Some(sc) = param_type.storage_class {
                        self.err(SemanticError::ParameterStorageClass(sc), location);
                    }
                    let id = if let Some(name) = param.declarator.id {
                        // int f(int a, int a)
                        if names.contains(&name) {
                            self.err(SemanticError::DuplicateParameter(name), location)
                        }
                        names.insert(name);
                        name
                    } else {
                        // int f(int)
                        InternedStr::default()
                    };
                    let meta = Variable {
                        ctype: param_type.ctype,
                        id,
                        qualifiers: param_type.qualifiers,
                        storage_class: StorageClass::Auto,
                    };
                    params.push(meta);
                }
                // int f(void);
                let is_void = match params.as_slice() {
                    [Variable {
                        ctype: Type::Void, ..
                    }] => true,
                    _ => false,
                };
                // int f(void, int) or int f(int, void) or ...
                if !is_void
                    && params.iter().any(|param| match param.ctype {
                        Type::Void => true,
                        _ => false,
                    })
                {
                    self.err(SemanticError::InvalidVoidParameter, location);
                // int f(void, ...)
                } else if func.varargs && is_void {
                    self.err(SemanticError::VoidVarargs, location);
                // int f(...)
                } else if func.varargs && params.is_empty() {
                    self.err(SemanticError::VarargsWithoutParam, location);
                }
                Type::Function(FunctionType {
                    params: params.into_iter().map(|m| m.insert()).collect(),
                    return_type: Box::new(return_type),
                    varargs: func.varargs,
                })
            }
        }
    }
    // used for arrays like `int a[BUF_SIZE - 1];` and enums like `enum { A = 1 }`
    fn const_literal(expr: Expr) -> CompileResult<LiteralValue> {
        let location = expr.location;
        expr.const_fold()?.into_literal().map_err(|runtime_expr| {
            Locatable::new(SemanticError::NotConstant(runtime_expr).into(), location)
        })
    }
    /// Return an unsigned integer that can be evaluated at compile time, or an error otherwise.
    fn const_uint(expr: Expr) -> CompileResult<crate::arch::SIZE_T> {
        use LiteralValue::*;

        let location = expr.location;
        match Self::const_literal(expr)? {
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
    /// Return a signed integer that can be evaluated at compile time, or an error otherwise.
    fn const_sint(expr: Expr) -> CompileResult<i64> {
        use LiteralValue::*;

        let location = expr.location;
        match Self::const_literal(expr)? {
            UnsignedInt(u) => match u.try_into() {
                Ok(i) => Ok(i),
                Err(_) => Err(Locatable::new(
                    SemanticError::ConstOverflow { is_positive: true }.into(),
                    location,
                )),
            },
            Int(i) => Ok(i),
            Char(c) => Ok(c.into()),
            Str(_) | Float(_) => Err(Locatable::new(
                SemanticError::NonIntegralLength.into(),
                location,
            )),
        }
    }
    /// Given some variable that we've already parsed (`decl`), perform various checks and add it to the current scope.
    ///
    /// In particular, this checks that
    /// - for any function `main()`, it has a signature compatible with that required by the C standard
    /// - either this variable has not yet been seen in this scope
    ///     - or it is a global variable that is compatible with the previous declaration (see below)
    ///
    /// This returns an opaque index to the `Metadata`.
    fn declare(&mut self, mut decl: Variable, init: bool, location: Location) -> Symbol {
        if decl.id == "main".into() {
            if let Type::Function(ftype) = &decl.ctype {
                // int main(int)
                if !ftype.is_main_func_signature() {
                    self.err(SemanticError::IllegalMainSignature, location);
                }
            }
        }
        // e.g. extern int i = 1;
        // this is a silly thing to do, but valid: https://stackoverflow.com/a/57900212/7669110
        if decl.storage_class == StorageClass::Extern && !decl.ctype.is_function() && init {
            self.warn(Warning::ExtraneousExtern, location);
            decl.storage_class = StorageClass::Auto;
        }
        let id = decl.id;
        let symbol = decl.insert();
        if let Some(existing_ref) = self.scope.insert(id, symbol) {
            let existing = existing_ref.get();
            let meta = symbol.get();
            // 6.2.2p4
            // > For an identifier declared with the storage-class specifier extern in a scope in which a prior declaration of that identifier is visible,
            // > if the prior declaration specifies internal or external linkage,
            // > the linkage of the identifier at the later declaration is the same as the linkage specified at the prior declaration.
            // > If no prior declaration is visible, or if the prior declaration specifies no linkage, then the identifier has external linkage.
            //
            // i.e. `static int f(); int f();` is the same as `static int f(); static int f();`
            // special case redefining the same type
            if self.scope.is_global()
                // int i; int i;
                && (existing == meta
                    // `static int i; extern int i;` or `int i; extern int i;`
                    || ((existing.storage_class == StorageClass::Static
                        || existing.storage_class == StorageClass::Auto)
                        && meta.storage_class == StorageClass::Extern)
                    // 6.2.2
                    // > For an identifier declared with the storage-class specifier extern ...
                    // > If no prior declaration is visible ... then the identifier has external linkage.
                    // and also
                    // > 3 If the declaration of a file scope identifier for an object contains the storage- class specifier static, the identifier has internal linkage.
                    // so since
                    // > If, within a translation unit, the same identifier appears with both internal and external linkage, the behavior is undefined.

                    // extern int i; int i;
                    || (existing.storage_class == StorageClass::Extern && meta.storage_class != StorageClass::Static))
            {
                // int i = 1; int i = 2;
                if init && self.initialized.contains(&existing_ref) {
                    self.err(SemanticError::Redefinition(id), location);
                }
            } else {
                // extern int i; static int i;
                let err = SemanticError::IncompatibleRedeclaration(id, existing_ref, symbol);
                self.err(err, location);
            }
        }
        symbol
    }
}

impl types::FunctionType {
    // check if this is a valid signature for 'main'
    fn is_main_func_signature(&self) -> bool {
        // main must return 'int' and must not be variadic
        if *self.return_type != Type::Int(true) || self.varargs {
            return false;
        }
        // allow 'main()''
        if self.params.is_empty() {
            return true;
        }
        // so the borrow-checker doesn't complain
        let meta: Vec<_> = self.params.iter().map(|param| param.get()).collect();
        let types: Vec<_> = meta.iter().map(|param| &param.ctype).collect();
        match types.as_slice() {
            // allow 'main(void)'
            [Type::Void] => true,
            // TODO: allow 'int main(int argc, char *argv[], char *environ[])'
            [Type::Int(true), Type::Pointer(t, _)] | [Type::Int(true), Type::Array(t, _)] => {
                match &**t {
                    Type::Pointer(inner, _) => inner.is_char(),
                    _ => false,
                }
            }
            _ => false,
        }
    }
}

impl Type {
    #[inline]
    fn is_char(&self) -> bool {
        match self {
            Type::Char(true) => true,
            _ => false,
        }
    }
}

/// Analyze a single function
///
/// This is separate from `Analyzer` so that `metadata` does not have to be an `Option`.
struct FunctionAnalyzer<'a> {
    /// the function we are currently compiling.
    /// used for checking return types
    metadata: FunctionData,
    /// We need this for the scopes, as well as for parsing expressions
    analyzer: &'a mut PureAnalyzer,
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

impl FunctionAnalyzer<'_> {
    /// Performs semantic analysis on the function and adds it to `METADATA_STORE`.
    /// Returns the analyzed statements.
    fn analyze(
        func: ast::FunctionDefinition,
        analyzer: &mut PureAnalyzer,
        location: Location,
    ) -> (Symbol, Vec<Stmt>) {
        let parsed_func = analyzer.parse_type(func.specifiers, func.declarator.into(), location);
        // saltwater ignores `inline` and `_Noreturn`
        if parsed_func.qualifiers != Qualifiers::default() {
            analyzer.error_handler.warn(
                Warning::FunctionQualifiersIgnored(parsed_func.qualifiers),
                location,
            );
        }
        let sc = match parsed_func.storage_class {
            None => StorageClass::Extern,
            Some(sc @ StorageClass::Extern) | Some(sc @ StorageClass::Static) => sc,
            // auto int f();
            Some(other) => {
                analyzer.err(SemanticError::InvalidFuncStorageClass(other), location);
                StorageClass::Extern
            }
        };
        let metadata = Variable {
            ctype: parsed_func.ctype.clone(),
            id: func.id,
            qualifiers: parsed_func.qualifiers,
            storage_class: sc,
        };
        let symbol = analyzer.declare(metadata, true, location);
        let func_type = match parsed_func.ctype {
            Type::Function(ftype) => ftype,
            _ => unreachable!(),
        };
        // used for figuring out what casts `return 1;` should make
        let tmp_metadata = FunctionData {
            location,
            id: func.id,
            return_type: *func_type.return_type,
        };
        assert!(analyzer.scope.is_global());
        assert!(analyzer.tag_scope.is_global());
        let mut func_analyzer = FunctionAnalyzer {
            metadata: tmp_metadata,
            analyzer,
        };
        func_analyzer.enter_scope();
        for (i, param) in func_type.params.into_iter().enumerate() {
            let meta = param.get();
            if meta.id == InternedStr::default() && meta.ctype != Type::Void {
                // int f(int) {}
                func_analyzer.err(
                    SemanticError::MissingParamName(i, meta.ctype.clone()),
                    location,
                );
            }
            // TODO: I think this should go through `declare` instead,
            // but that requires having a mutable `Metadata`
            func_analyzer.analyzer.scope.insert(meta.id, param);
        }
        let stmts = func
            .body
            .into_iter()
            .map(|s| func_analyzer.parse_stmt(s))
            .collect();
        // TODO: this location should be the end of the function, not the start
        func_analyzer.leave_scope(location);
        assert!(analyzer.tag_scope.is_global());
        assert!(analyzer.scope.is_global());
        (symbol, stmts)
    }
}

impl FunctionAnalyzer<'_> {
    fn err(&mut self, err: SemanticError, location: Location) {
        self.analyzer.err(err, location);
    }
    fn enter_scope(&mut self) {
        self.analyzer.scope.enter();
        self.analyzer.tag_scope.enter();
    }
    fn leave_scope(&mut self, location: Location) {
        for object in self.analyzer.scope.get_all_immediate().values() {
            let object = object.get();
            match &object.ctype {
                Type::Struct(StructType::Named(name, members))
                | Type::Union(StructType::Named(name, members)) => {
                    if members.get().is_empty()
                        // `extern struct s my_s;` and `typedef struct s S;` are fine
                        && object.storage_class != StorageClass::Extern
                        && object.storage_class != StorageClass::Typedef
                    {
                        // struct s my_s;
                        self.analyzer.error_handler.error(
                            SemanticError::ForwardDeclarationIncomplete(*name, object.id),
                            location,
                        );
                    }
                }
                _ => {}
            }
        }
        self.analyzer.scope.exit();
        self.analyzer.tag_scope.exit();
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
    specifiers: Vec<DeclarationSpecifier>,
    error_handler: &mut ErrorHandler,
    location: Location,
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
            if spec.is_type() {
                let err = SemanticError::InvalidSpecifier {
                    existing: spec.into(),
                    new: spec.into(),
                };
                error_handler.error(err, location);
            } else {
                error_handler.warn(Warning::DuplicateSpecifier(spec, count), location);
            }
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
    /// Returns whether this is a self-contained type, not just whether this modifies a type.
    /// For example, `int` and `long` are self-contained types, but `unsigned` and `_Complex` are not.
    /// This is despite the fact that `unsigned i;` is valid and means `unsigned int i;`
    fn is_type(self) -> bool {
        use UnitSpecifier::*;
        match self {
            Bool | Char | Int | Long | Float | Double | VaList => true,
            _ => false,
        }
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::{Error, *};
    use crate::data::types::{ArrayType, FunctionType, Type::*};
    use crate::lex::PreProcessor;
    use crate::parse::test::*;

    pub(crate) fn analyze<'c, 'input: 'c, P, A, R, S, E>(
        input: &'input str,
        parse_func: P,
        analyze_func: A,
    ) -> CompileResult<R>
    where
        P: Fn(&mut Parser<PreProcessor<'c>>) -> Result<S, E>,
        A: Fn(&mut PureAnalyzer, S) -> R,
        CompileError: From<E>,
    {
        let mut p = parser(input);
        let ast = parse_func(&mut p)?;
        let mut a = PureAnalyzer::new();
        let e = analyze_func(&mut a, ast);
        if let Some(err) = a.error_handler.pop_front() {
            return Err(err);
        }
        Ok(e)
    }

    fn maybe_decl(s: &str) -> Option<CompileResult<Declaration>> {
        decls(s).into_iter().next()
    }

    pub(crate) fn decl(s: &str) -> CompileResult<Declaration> {
        maybe_decl(s).unwrap_or_else(|| panic!("expected a declaration or error: '{}'", s))
    }

    pub(crate) fn decls(s: &str) -> Vec<CompileResult<Declaration>> {
        Analyzer::new(parser(s), false)
            .map(|o| o.map(|l| l.data))
            .collect()
    }

    pub(crate) fn assert_errs_decls(input: &str, errs: usize, warnings: usize, decls: usize) {
        let mut a = Analyzer::new(parser(input), false);
        let (mut a_errs, mut a_decls) = (0, 0);
        for res in &mut a {
            if res.is_err() {
                a_errs += 1;
            } else {
                a_decls += 1;
            }
        }
        let a_warns = a.inner.error_handler.warnings.len();

        if (a_errs, a_warns, a_decls) != (errs, warnings, decls) {
            println!(
                "({} errs, {} warnings, {} decls) != ({}, {}, {}) when parsing {}",
                a_errs, a_warns, a_decls, errs, warnings, decls, input
            );
            println!("note: warnings:");
            for warning in a.inner.error_handler.warnings {
                println!("- {}", warning.data);
            }
        };
    }

    pub(crate) fn analyze_expr(s: &str) -> CompileResult<Expr> {
        analyze(s, Parser::expr, PureAnalyzer::expr)
    }

    pub(crate) fn assert_decl_display(left: &str, right: &str) {
        assert_eq!(decl(left).unwrap().to_string(), right);
    }
    fn assert_extern_decl_display(s: &str) {
        assert_decl_display(s, s);
    }

    pub(super) fn assert_same(left: &str, right: &str) {
        assert_eq!(
            decl(left).unwrap().to_string(),
            decl(right).unwrap().to_string()
        );
    }
    pub(crate) fn assert_no_change(s: &str) {
        assert_decl_display(s, s);
    }

    fn match_type(lexed: CompileResult<Declaration>, given_type: Type) -> bool {
        fn type_helper(ctype: &Type, given_type: &Type) -> bool {
            match (ctype, given_type) {
                // because the parameters use `MetadataRef`,
                // it's impossible to have the same ref twice, even in unit tess
                (Type::Function(actual), Type::Function(expected)) => {
                    // TODO: this only handles one level of function nesting
                    actual
                        .params
                        .iter()
                        .zip(&expected.params)
                        .all(|(left, right)| metadata_helper(&left.get(), &right.get()))
                        && {
                            println!("all params match");
                            true
                        }
                        && dbg!(type_helper(&actual.return_type, &expected.return_type))
                        && dbg!(actual.varargs == expected.varargs)
                }
                (Type::Pointer(a, lq), Type::Pointer(b, rq)) => type_helper(&*a, &*b) && lq == rq,
                (Type::Array(a, la), Type::Array(b, ra)) => type_helper(&*a, &*b) && la == ra,
                (a, b) => a == b,
            }
        }
        fn metadata_helper(left: &Variable, right: &Variable) -> bool {
            dbg!(type_helper(dbg!(&left.ctype), dbg!(&right.ctype)))
                && left.storage_class == right.storage_class
                && left.qualifiers == right.qualifiers
                && left.id == right.id
        }
        lexed.map_or(false, |decl| {
            type_helper(&decl.symbol.get().ctype, &given_type)
        })
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
        assert_extern_decl_display("int i;");
        assert_eq!(
            decl("extern int i;").unwrap().symbol.get().storage_class,
            StorageClass::Extern
        );
        assert_eq!(
            decl("static int i;").unwrap().symbol.get().storage_class,
            StorageClass::Static
        );
        match decl("auto int i;").unwrap_err().data {
            Error::Semantic(SemanticError::AutoAtGlobalScope) => {}
            _ => panic!("wrong error"),
        }
    }

    #[test]
    fn function() {
        assert_extern_decl_display("int f();");
        assert_extern_decl_display("int f(int i);");
        assert_extern_decl_display("int f(int i, int j);");
        // functions decay to pointers when used as parameters
        assert_same("int f(int g());", "int f(int (*g)());");
        assert_same("int f(int g(), ...);", "int f(int (*g)(), ...);");
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
        assert!(match_type(decl("long double d;"), Type::Double));
        assert!(match_type(decl("short int i;"), Type::Short(true)));
        assert!(match_type(decl("long int i;"), Type::Long(true)));
        assert!(match_type(decl("long long int i;"), Type::Long(true)));
    }
    #[test]
    fn test_bad_decl_specs() {
        assert!(maybe_decl("int;").is_none());
        for s in &[
            "char char i;",
            "char int i",
            "_Bool int i",
            "float int i",
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
            assert!(decl(s).is_err(), "'{}' should be an error", s);
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
        assert_extern_decl_display("int a[1];");
        assert_same("int a[(int)1];", "int a[1];");
    }
    #[test]
    fn test_pointers() {
        for &pointer in &[
            "void *a;",
            "float *const a;",
            "double *volatile *const a;",
            "double *volatile *const a;",
            "_Bool *const volatile a;",
        ] {
            assert_extern_decl_display(pointer);
        }
    }
    #[test]
    fn test_pointers_and_arrays() {
        // cdecl: declare foo as array 10 of pointer to pointer to char
        assert!(match_type(
            decl("char **foo[10];"),
            Array(
                Box::new(Pointer(
                    Box::new(Pointer(Box::new(Char(true)), Qualifiers::default(),)),
                    Qualifiers::default(),
                )),
                ArrayType::Fixed(10),
            )
        ));
        // cdecl: declare foo as pointer to pointer to array 10 of int
        assert!(match_type(
            decl("int (**foo)[10];"),
            Pointer(
                Box::new(Pointer(
                    Box::new(Array(Box::new(Int(true)), ArrayType::Fixed(10),)),
                    Qualifiers::default(),
                )),
                Qualifiers::default(),
            )
        ));
    }
    #[test]
    fn test_functions() {
        assert!(match_type(
            decl("void *f();"),
            Function(FunctionType {
                return_type: Box::new(Pointer(Box::new(Type::Void), Qualifiers::default())),
                params: vec![],
                varargs: false,
            })
        ));
        // cdecl: declare i as pointer to function returning int;
        assert!(match_type(
            decl("int (*i)();"),
            Pointer(
                Box::new(Function(FunctionType {
                    return_type: Box::new(Int(true)),
                    params: vec![],
                    varargs: false,
                })),
                Qualifiers::default()
            )
        ));
        // cdecl: declare i as pointer to function (int, char, float) returning int
        assert_no_change("extern int (*i)(int, char, float);");
        // cdecl: declare i as pointer to function (pointer to function returning int) returning int
        assert!(match_type(
            decl("int (*i)(int (*f)());"),
            Pointer(
                Box::new(Function(FunctionType {
                    return_type: Box::new(Int(true)),
                    params: vec![Variable {
                        id: InternedStr::get_or_intern("f"),
                        ctype: Pointer(
                            Box::new(Function(FunctionType {
                                return_type: Box::new(Int(true)),
                                params: vec![],
                                varargs: false
                            })),
                            Qualifiers::default()
                        ),
                        qualifiers: Default::default(),
                        storage_class: Default::default(),
                    }
                    .insert()],
                    varargs: false,
                })),
                Qualifiers::default()
            )
        ));
        assert!(match_type(
            decl("int f(int, ...);"),
            Function(FunctionType {
                return_type: Box::new(Int(true)),
                params: vec![Variable {
                    id: Default::default(),
                    ctype: Int(true),
                    qualifiers: Default::default(),
                    storage_class: Default::default()
                }
                .insert()],
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
                params: vec![Variable {
                    id: InternedStr::get_or_intern("a"),
                    ctype: Pointer(Box::new(Int(true)), Qualifiers::default()),
                    qualifiers: Default::default(),
                    storage_class: Default::default(),
                }
                .insert()],
                varargs: false
            })
        ));

        assert!(decl("int b[static 10];").is_err());
    }
    #[test]
    fn test_inline_keyword() {
        // Correct usage
        assert!(match_type(
            decl("inline void f(void);"),
            Function(FunctionType {
                return_type: Box::new(Void),
                params: vec![Variable {
                    id: InternedStr::default(),
                    ctype: Type::Void,
                    qualifiers: Qualifiers::default(),
                    storage_class: StorageClass::default(),
                }
                .insert()],
                varargs: false,
            })
        ));

        // `inline` is not allowed in the following cases
        assert!(decl("inline int a;").is_err()); // Normal declarations
        assert!(decl("void f(inline int a);").is_err()); // Parameter lists
        assert!(decl("struct F { inline int a; } f;").is_err()); // Struct members
        assert!(
            // Type names
            decl("int main() { char a = (inline char)(4); }").is_err()
        );
        assert!(decl("typedef a inline int;").is_err());
    }
    #[test]
    fn test_complex() {
        // cdecl: declare bar as const pointer to array 10 of pointer to function (int) returning volatile pointer to char
        assert!(match_type(
            decl("char * volatile (*(* const bar)[])(int );"),
            Pointer(
                Box::new(Array(
                    Box::new(Pointer(
                        Box::new(Function(FunctionType {
                            return_type: Box::new(Pointer(
                                Box::new(Char(true)),
                                Qualifiers {
                                    volatile: true,
                                    ..Qualifiers::default()
                                }
                            )),
                            params: vec![Variable {
                                ctype: Int(true),
                                storage_class: Default::default(),
                                id: Default::default(),
                                qualifiers: Qualifiers::NONE,
                            }
                            .insert()],
                            varargs: false,
                        })),
                        Qualifiers::default()
                    )),
                    ArrayType::Unbounded,
                )),
                Qualifiers {
                    c_const: true,
                    ..Qualifiers::default()
                }
            )
        ));
        // cdecl: declare foo as pointer to function (void) returning pointer to array 3 of int
        assert!(match_type(
            decl("int (*(*foo)(void))[];"),
            Pointer(
                Box::new(Function(FunctionType {
                    return_type: Box::new(Pointer(
                        Box::new(Array(Box::new(Int(true)), ArrayType::Unbounded)),
                        Qualifiers::default()
                    )),
                    params: vec![Variable {
                        ctype: Void,
                        storage_class: Default::default(),
                        id: Default::default(),
                        qualifiers: Default::default(),
                    }
                    .insert()],
                    varargs: false,
                })),
                Qualifiers::default()
            )
        ));
        // cdecl: declare bar as volatile pointer to array 64 of const int
        assert!(match_type(
            decl("const int (* volatile bar)[];"),
            Pointer(
                Box::new(Array(Box::new(Int(true)), ArrayType::Unbounded)),
                Qualifiers {
                    volatile: true,
                    ..Qualifiers::default()
                }
            )
        ));
        // cdecl: declare x as function returning pointer to array 5 of pointer to function returning char
        assert!(match_type(
            decl("char (*(*x())[])();"),
            Function(FunctionType {
                return_type: Box::new(Pointer(
                    Box::new(Array(
                        Box::new(Pointer(
                            Box::new(Function(FunctionType {
                                return_type: Box::new(Char(true)),
                                params: vec![],
                                varargs: false,
                            })),
                            Qualifiers::default()
                        )),
                        ArrayType::Unbounded
                    )),
                    Qualifiers::default()
                )),
                params: vec![],
                varargs: false,
            })
        ));
    }
    #[test]
    fn test_multiple() {
        assert_same("int i, j, k;", "int i; int j; int k;");
        assert_same(
            "char *p, c, **pp, f();",
            "char *p; char c; char **p; char f();",
        );
    }
    #[test]
    fn test_no_specifiers() {
        assert_same("i, j, k;", "int i, j, k;");
        assert_same("*p, c, **pp, f();", "int *p, c, **pp, f();");
    }
    #[test]
    fn test_decl_errors() {
        // no semicolon
        assert!(decl("int").is_err());
        assert!(decl("int i").is_err());
        // type error: cannot have array of functions or function returning array
        assert!(decl("int f()[];").is_err());
        assert!(decl("int f[]();").is_err());
        assert!(decl("int f()();").is_err());
        assert!(decl("int (*f)[;").is_err());
        // duplicate parameter name
        assert!(decl("int f(int a, int a);").is_err());
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
        assert_same(
            "static int f(); int f();",
            "static int f(); extern int f();",
        );

        // However the opposite should still error
        assert_errs_decls(
            "extern int f();
                static int f();",
            1,
            0,
            2,
        );
    }

    #[test]
    fn enum_declaration() {
        assert!(decl("enum;").is_err());
        assert!(decl("enum e;").is_err());
        assert!(decl("enum e {};").is_err());
        assert!(decl("enum e { A }").is_err());
        assert!(maybe_decl("enum { A };").is_none());
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
        let mut ds = decls("typedef unsigned uint; uint i;").into_iter();
        assert_eq!(
            ds.next().unwrap().unwrap().to_string(),
            "typedef unsigned int uint;"
        );
        assert_decl_display("unsigned int i;", &ds.next().unwrap().unwrap().to_string());
    }
    #[test]
    fn bitfields() {
        assert!(decl("struct { int:5; } a;").is_err());
        assert!(decl("struct { int a:5; } b;").is_ok());
        assert!(decl("struct { int a:5, b:6; } c;").is_ok());
        assert!(decl("struct { extern int a:5; } d;").is_err());
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
    #[test]
    fn redefinition_is_err() {
        assert_errs_decls("int i = 1, i = 2;", 1, 0, 2);
    }
    #[test]
    fn void() {
        assert_no_change("extern int f(void);");
        assert_no_change("extern int f(int);");
        assert!(decl("int f(int, void);").is_err());
        assert!(decl("int f(void, int);").is_err());
        assert!(decl("int f(void, void);").is_err());
        assert!(decl("int f(int) { return 1; }").is_err());
        assert_decl_display(
            "int f(void) { return 1; }",
            "extern int f(void) {\n    return (int)(1);\n}\n",
        );
    }
}
