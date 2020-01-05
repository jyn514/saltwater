use std::collections::{HashSet, VecDeque};
use std::convert::TryFrom;
use std::iter::{FromIterator, Iterator};
use std::mem;

use super::{FunctionData, Lexeme, Parser, TagEntry};
use crate::arch::SIZE_T;
use crate::data::{
    lex::Keyword,
    prelude::*,
    types::{ArrayType, FunctionType},
    Initializer, Qualifiers, StorageClass,
};
use crate::utils::warn;

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    /* grammar functions
     * this parser is a top-down, recursive descent parser
     * and uses a modified version of the ANSI C Yacc grammar published at
     * https://www.lysator.liu.se/c/ANSI-C-grammar-y.html.
     * Differences from the original grammar, if present, are noted
     * before each function.
     */

    /// type_name
    ///     : specifier_qualifier_list
    ///     | specifier_qualifier_list abstract_declarator
    ///     ;
    ///
    /// where specifier_qualifier_list: (type_specifier | type_qualifier)+
    ///
    /// Used for casts and `sizeof` builtin.
    pub fn type_name(&mut self) -> Result<Locatable<(Type, Qualifiers)>, SyntaxError> {
        let (sc, qualifiers, ctype, _) = self.declaration_specifiers()?;
        if sc != None {
            self.semantic_err("type cannot have a storage class", self.last_location);
        }
        let ctype = match self.declarator(true, qualifiers)? {
            None => ctype,
            Some(decl) => {
                let (id, ctype) = decl
                    .parse_type(ctype, false, &self.last_location)
                    .recover(&mut self.error_handler);
                if let Some(Locatable {
                    location,
                    data: name,
                }) = id
                {
                    self.semantic_err(
                        format!("abstract types cannot have an identifier (got '{}')", name),
                        location,
                    );
                }
                ctype
            }
        };
        Ok(Locatable {
            location: self.last_location,
            data: (ctype, qualifiers),
        })
    }

    /* NOTE: there's some fishiness here. Declarations can have multiple variables,
     * but we typed them as only having one Symbol. Wat do?
     * We push all but one declaration into the 'pending' vector
     * and return the last.
     */
    pub fn declaration(&mut self) -> Result<VecDeque<Locatable<Declaration>>, SyntaxError> {
        let (sc, mut qualifiers, ctype, seen_compound_type) = self.declaration_specifiers()?;
        if self.match_next(&Token::Semicolon).is_some() {
            if !seen_compound_type {
                warn(
                    "declaration does not declare anything",
                    self.next_location(),
                );
            }
            return Ok(VecDeque::new());
        }

        // special case functions bodies - they can only occur as the first declarator
        let declarator = self
            .declarator(false, qualifiers)?
            .expect("declarator should return id when called with allow_abstract: false");
        let (id, first_type) = declarator
            .parse_type(
                ctype.clone(),
                sc == Some(StorageClass::Typedef),
                &self.last_location,
            )
            .recover(&mut self.error_handler);
        let id = id.expect("declarator should return id when called with allow_abstract: false");
        let sc = match sc {
            Some(sc) => sc,
            None if first_type.is_function() => StorageClass::Extern,
            None => StorageClass::Auto,
        };
        if sc == StorageClass::Typedef {
            // evaluated only for its side effects
            self.parse_typedef(id, first_type, qualifiers)?;
            return Ok(VecDeque::new());
        }

        let mut symbol = Symbol {
            id: id.data,
            ctype: first_type,
            qualifiers,
            storage_class: sc,
            init: false,
        };
        // if it's not a function, we still need to handle it
        let init = match (&symbol.ctype, self.peek_token()) {
            (Type::Function(ftype), Some(Token::LeftBrace)) => {
                symbol.init = true;
                let ftype = ftype.clone();
                self.declare(&mut symbol, &id.location);
                Some(Initializer::FunctionBody(self.function_body(
                    symbol.id.clone(),
                    ftype,
                    id.location.clone(),
                )?))
            }
            (Type::Function(_), Some(t)) if *t == Token::EQUAL => {
                return Err(SyntaxError(Locatable {
                    data: format!(
                        "expected '{{', got '=' while parsing function body for {}",
                        symbol.id,
                    ),
                    location: id.location,
                }));
            }
            (ctype, Some(t)) if *t == Token::EQUAL => {
                self.next_token();
                let init = Some(self.initializer(ctype)?);
                symbol.init = true;
                self.declare(&mut symbol, &id.location);
                init
            }
            _ => {
                self.declare(&mut symbol, &id.location);
                None
            }
        };
        if symbol.ctype.is_function() && (qualifiers.c_const || qualifiers.volatile) {
            warn(
                &format!("{} has no effect on function return type", qualifiers),
                id.location,
            );
            qualifiers.c_const = false;
            qualifiers.volatile = false;
        }
        let decl = Locatable {
            data: Declaration { symbol, init },
            location: id.location,
        };
        let init = decl.data.init.is_some();
        let is_function = decl.data.symbol.ctype.is_function();
        let mut pending = VecDeque::from_iter(std::iter::once(decl));
        if (is_function && init) || self.match_next(&Token::Semicolon).is_some() {
            return Ok(pending);
        } else {
            self.expect(Token::Comma)?;
        }
        loop {
            let mut decl = self.init_declarator(sc, qualifiers, ctype.clone())?;
            self.declare(&mut decl.data.symbol, &decl.location);
            pending.push_back(decl);
            if self.match_next(&Token::Comma).is_none() {
                self.expect(Token::Semicolon)?;
                break;
            }
        }
        Ok(pending)
    }
    // check if this is a valid signature for 'main'
    fn is_main_func_signature(ftype: &FunctionType) -> bool {
        // main must return 'int' and must not be variadic
        if *ftype.return_type != Type::Int(true) || ftype.varargs {
            return false;
        }
        // allow 'main()''
        if ftype.params.is_empty() {
            return true;
        }
        let types: Vec<&Type> = ftype.params.iter().map(|param| &param.ctype).collect();
        // allow 'main(void)'
        if types == vec![&Type::Void] {
            return true;
        }
        // TODO: allow 'int main(int argc, char *argv[], char *environ[])'
        if types.len() != 2 || *types[0] != Type::Int(true) {
            return false;
        }
        match types[1] {
            Type::Pointer(t) | Type::Array(t, _) => match &**t {
                Type::Pointer(inner) => inner.is_char(),
                _ => false,
            },
            _ => false,
        }
    }
    fn parse_typedef(
        &mut self,
        first_id: Locatable<InternedStr>,
        first_ctype: Type,
        first_qualifiers: Qualifiers,
    ) -> Result<(), SyntaxError> {
        self.declare_typedef(first_id, first_ctype.clone(), first_qualifiers);
        if self.match_next(&Token::Semicolon).is_some() {
            return Ok(());
        }
        self.expect(Token::Comma)?;
        loop {
            let decl = self
                .declarator(false, first_qualifiers)?
                .expect("declarator should return Some when called with allow_abstract: false");
            let location = decl.id().unwrap().location;
            let (id, ctype) = decl
                .parse_type(first_ctype.clone(), true, &location)
                .recover(&mut self.error_handler);
            let id = id.unwrap();
            self.declare_typedef(id, ctype, first_qualifiers);
            if self.match_next(&Token::Comma).is_none() {
                self.expect(Token::Semicolon)?;
                return Ok(());
            }
        }
    }
    fn declare_typedef(&mut self, id: Locatable<InternedStr>, ctype: Type, qualifiers: Qualifiers) {
        if qualifiers.inline {
            self.semantic_err(
                "`inline` is only allowed on function declarations",
                id.location,
            );
        }
        let typedef = Symbol {
            id: id.data,
            ctype: ctype.clone(),
            qualifiers,
            storage_class: StorageClass::Typedef,
            init: true,
        };
        if let Some(existing_def) = self.scope.insert(id.data.clone(), typedef) {
            let message = if existing_def.storage_class == StorageClass::Typedef {
                // special case redefining the same type
                if existing_def.ctype == ctype {
                    return;
                }
                format!(
                    "typedef '{}' for '{}' cannot be redefined as different type '{}'",
                    existing_def.ctype, id.data, ctype
                )
            } else {
                format!("cannot redefine variable '{}' as typedef", id.data)
            };
            self.semantic_err(message, id.location);
        }
    }
    fn declare(&mut self, decl: &mut Symbol, location: &Location) {
        if decl.id == InternedStr::get_or_intern("main") {
            if let Type::Function(ftype) = &decl.ctype {
                if !Self::is_main_func_signature(ftype) {
                    self.semantic_err(
                        "illegal signature for main function (expected 'int main(void)' or 'int main(int, char **)'",
                        *location,
                    );
                }
            }
        }
        // e.g. extern int i = 1;
        // this is a silly thing to do, but valid: https://stackoverflow.com/a/57900212/7669110
        if decl.storage_class == StorageClass::Extern && !decl.ctype.is_function() && decl.init {
            crate::utils::warn(
                "this is a definition, not a declaration, the 'extern' keyword has no effect",
                *location,
            );
            decl.storage_class = StorageClass::Auto;
        }
        if let Some(existing) = self.scope.get_immediate(&decl.id) {
            if existing == decl {
                if decl.init && existing.init {
                    self.semantic_err(format!("redefinition of '{}'", decl.id), *location);
                }
            } else {
                let err = format!(
                    "redeclaration of '{}' with different type or qualifiers (originally {}, now {})",
                    existing.id, existing, decl
                );
                self.semantic_err(err, *location);
            }
            self.scope.insert(decl.id.clone(), decl.clone());
        } else {
            self.scope.insert(decl.id.clone(), decl.clone());
        }
    }
    fn init_declarator(
        &mut self,
        sc: StorageClass,
        qualifiers: Qualifiers,
        ctype: Type,
    ) -> Result<Locatable<Declaration>, SyntaxError> {
        // parse declarator
        // declarator: Result<Symbol, SyntaxError>
        let decl = self
            .declarator(false, qualifiers)?
            .expect("declarator should never return None when called with allow_abstract: false");
        let (id, ctype) = decl
            .parse_type(ctype, false, &self.last_location)
            .recover(&mut self.error_handler);
        let id = id.expect("declarator should return id when called with allow_abstract: false");

        // optionally, parse an initializer
        let init = if self.match_next(&Token::EQUAL).is_some() {
            Some(self.initializer(&ctype)?)
        } else {
            None
        };

        // clean up and go home
        let symbol = Symbol {
            id: id.data,
            qualifiers,
            storage_class: if sc == StorageClass::Auto && ctype.is_function() {
                StorageClass::Extern
            } else {
                sc
            },
            ctype,
            init: init.is_some(),
        };
        Ok(Locatable {
            data: Declaration { symbol, init },
            location: id.location,
        })
    }
    /* this is an utter hack
     * NOTE: the reason the return type is so weird (Result<_, Locatable<_>)
     * is because declaration specifiers can never be a statement on their own:
     * the associated location always belongs to the identifier
     *
     * reference grammar:
     * declaration_specifiers
     *  : storage_class_specifier
     *  | storage_class_specifier declaration_specifiers
     *  | type_specifier
     *  | type_specifier declaration_specifiers
     *  | type_qualifier
     *  | type_qualifier declaration_specifiers
     *  ;
     */
    fn declaration_specifiers(
        &mut self,
    ) -> Result<(Option<StorageClass>, Qualifiers, Type, bool), SyntaxError> {
        // TODO: initialization is a mess
        let mut keywords = HashSet::new();
        let mut storage_class = None;
        let mut qualifiers = Qualifiers::NONE;
        let mut ctype = None;
        let mut signed = None;
        let mut seen_compound = false;
        let mut seen_typedef = false;
        if self.peek_token().is_none() {
            return Err(SyntaxError(Locatable {
                data: "expected declaration specifier, got <end-of-file>".into(),
                location: self.last_location,
            }));
        }
        // unsigned const int
        while let Some(locatable) = self.next_token() {
            let (location, keyword) = match locatable.data {
                Token::Keyword(kind @ Keyword::Struct)
                | Token::Keyword(kind @ Keyword::Union)
                | Token::Keyword(kind @ Keyword::Enum) => {
                    if let Some(ctype) = &ctype {
                        self.semantic_err(
                            format!(
                                "cannot combine '{}' specifier with previous '{}' type specifier",
                                locatable.data, ctype
                            ),
                            locatable.location,
                        );
                    } else {
                        ctype = Some(self.compound_specifier(kind, locatable.location)?);
                        seen_compound = true;
                    }
                    continue;
                }
                Token::Keyword(k) if k.is_decl_specifier() => (locatable.location, k),
                Token::Id(id) => match self.scope.get(&id) {
                    Some(typedef)
                        if typedef.storage_class == StorageClass::Typedef && !seen_typedef =>
                    {
                        ctype = Some(typedef.ctype.clone());
                        seen_typedef = true;
                        continue;
                    }
                    _ => {
                        self.unput(Some(Locatable {
                            data: Token::Id(id),
                            location: locatable.location,
                        }));
                        break;
                    }
                },
                _ => {
                    self.unput(Some(locatable));
                    break;
                }
            };
            if keywords.insert(keyword) {
                self.declaration_specifier(
                    keyword,
                    &mut storage_class,
                    &mut qualifiers,
                    &mut ctype,
                    &mut signed,
                    location,
                );
            } else {
                // duplicate
                // we can guess that they just meant to write it once
                if keyword.is_qualifier()
                    || keyword.is_storage_class()
                    || keyword == Keyword::Signed
                    || keyword == Keyword::Unsigned
                {
                    warn(
                        &format!("duplicate declaration specifier '{}'", keyword),
                        location,
                    );
                // what is `short short` supposed to be?
                } else if keyword != Keyword::Long {
                    self.semantic_err(
                        format!("duplicate basic type '{}' in declarator", keyword),
                        location,
                    );
                }
            }
        }
        let ctype = match ctype {
            Some(Type::Char(ref mut s))
            | Some(Type::Short(ref mut s))
            | Some(Type::Int(ref mut s))
            | Some(Type::Long(ref mut s)) => {
                if let Some(explicit) = signed {
                    *s = explicit;
                }
                ctype.unwrap()
            }
            Some(ctype) => ctype,
            None => {
                if signed.is_none() {
                    // if it's not an id, it's invalid anyway
                    // other parts of the parser will have a better error message
                    if let Some(Token::Id(_)) = self.peek_token() {
                        warn(
                            "type specifier missing, defaults to int",
                            self.next_location(),
                        );
                    }
                }
                Type::Int(signed.unwrap_or(true))
            }
        };
        Ok((storage_class, qualifiers, ctype, seen_compound))
    }
    /*
    rewritten grammar:

    struct_or_union_specifier
    : (struct | union) '{' struct_declaration + '}'
    | (struct | union) identifier '{' struct_declaration + '}'
    | (struct | union) identifier
    ;

    enum_specifier
        : ENUM '{' enumerator_list '}'
        | ENUM identifier '{' enumerator_list '}'
        | ENUM identifier
        ;
    */
    fn compound_specifier(
        &mut self,
        kind: Keyword,
        location: Location,
    ) -> Result<Type, SyntaxError> {
        use std::rc::Rc;
        let ident = match self.match_next(&Token::Id(Default::default())) {
            Some(Locatable {
                data: Token::Id(data),
                location,
            }) => Some(Locatable { data, location }),
            None => None,
            _ => unreachable!("match_next"),
        };
        if self.match_next(&Token::LeftBrace).is_none() {
            let (ident, location) = match ident {
                Some(token) => (token.data, token.location),
                // struct *s; or struct;
                None => {
                    self.semantic_err(
                        format!("bare {} as type specifier is not allowed", kind),
                        location,
                    );
                    return Ok(match kind {
                        Keyword::Struct => Type::Struct(StructType::Anonymous(Rc::new(vec![]))),
                        Keyword::Union => Type::Union(StructType::Anonymous(Rc::new(vec![]))),
                        Keyword::Enum => Type::Enum(None, vec![]),
                        _ => unreachable!(),
                    });
                }
            };
            let has_semicolon = self.peek_token() == Some(&Token::Semicolon);
            let entry = match self.tag_scope.get(&ident) {
                Some(entry) => entry,
                // struct s;
                None => return Ok(self.forward_declaration(kind, ident, location)),
            };
            if has_semicolon && self.tag_scope.get_immediate(&ident).is_none() {
                // struct s; { union s; }
                return Ok(self.forward_declaration(kind, ident, location));
            }
            // struct s; struct s;
            return match entry {
                TagEntry::Struct(struct_ref) => {
                    let s = *struct_ref;
                    if kind != Keyword::Struct {
                        self.semantic_err(format!("use of '{}' with type tag '{}' that does not match previous struct declaration", ident, kind), location);
                    }
                    Ok(Type::Struct(StructType::Named(ident, s)))
                }
                TagEntry::Union(struct_ref) => {
                    let s = *struct_ref;
                    if kind != Keyword::Union {
                        self.semantic_err(format!("use of '{}' with type tag '{}' that does not match previous union declaration", ident, kind), location);
                    }
                    Ok(Type::Union(StructType::Named(ident, s)))
                }
                TagEntry::Enum(members) => {
                    let members = members.clone();
                    if kind != Keyword::Enum {
                        let err = format!("use of '{}' with type tag '{}' that does not match previous enum declaration", ident, kind);
                        self.semantic_err(err, location);
                    }
                    Ok(Type::Enum(Some(ident), members))
                }
            };
        }
        if let Some(locatable) = self.match_next(&Token::RightBrace) {
            self.semantic_err(format!("cannot have an empty {}", kind), locatable.location);
        }
        let ident = ident.map(|loc| loc.data);
        let ctype = if kind == Keyword::Enum {
            self.enumerators(ident, location)
        } else {
            self.struct_declaration(ident, kind == Keyword::Struct, &location)
        }?;
        self.expect(Token::RightBrace)?;
        Ok(ctype)
    }
    fn forward_declaration(
        &mut self,
        kind: Keyword,
        ident: InternedStr,
        location: Location,
    ) -> Type {
        if kind == Keyword::Enum {
            // see section 6.7.2.3 of the C11 standard
            self.semantic_err(
                format!("cannot have forward reference to enum type '{}'", ident),
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
    /* rewritten grammar:
    enumerator_list: enumerator (',' enumerator)* ;
    enumerator: identifier ('=' constant_expr)? ;
    */
    fn enumerators(
        &mut self,
        ident: Option<InternedStr>,
        location: Location,
    ) -> Result<Type, SyntaxError> {
        let mut current = 0;
        let mut members = vec![];
        loop {
            let member = self.expect(Token::Id(Default::default()))?;
            let name = match member.data {
                Token::Id(id) => id,
                _ => unreachable!("expect is broken"),
            };
            if self.match_next(&Token::EQUAL).is_some() {
                let constant = self.constant_expr()?.constexpr().unwrap_or_else(|err| {
                    let location = err.location();
                    self.error_handler.push_back(err);
                    Locatable::new((Literal::Int(-1), Type::Error), location)
                });
                current = match constant.data.0 {
                    Literal::Int(i) => i,
                    Literal::UnsignedInt(u) => match i64::try_from(u) {
                        Ok(i) => i,
                        Err(_) => {
                            self.semantic_err(
                                "values between INT_MAX and UINT_MAX are not supported for enums",
                                constant.location,
                            );
                            std::i64::MAX
                        }
                    },
                    Literal::Char(c) => i64::from(c),
                    _ => {
                        self.semantic_err(
                            "expression is not an integer constant",
                            constant.location,
                        );
                        0
                    }
                };
            }
            members.push((name, current));
            // TODO: this is such a hack
            let tmp_symbol = Symbol {
                id: name,
                qualifiers: Qualifiers::CONST,
                storage_class: StorageClass::Register,
                init: true,
                ctype: Type::Enum(None, vec![(name, current)]),
            };
            self.scope.insert(name, tmp_symbol);
            // allow trailing commas
            if self.match_next(&Token::Comma).is_none()
                || self.peek_token() == Some(&Token::RightBrace)
            {
                break;
            }
            current += 1;
        }
        for (name, _) in &members {
            self.scope._remove(name);
        }
        if let Some(id) = &ident {
            if self
                .tag_scope
                .insert(id.clone(), TagEntry::Enum(members.clone()))
                .is_some()
            {
                self.semantic_err(format!("redefition of enum '{}'", id), location);
            }
        }
        let ctype = Type::Enum(ident, members);
        match &ctype {
            Type::Enum(_, members) => {
                for (id, _) in members {
                    self.scope.insert(
                        id.clone(),
                        Symbol {
                            id: *id,
                            init: true,
                            storage_class: StorageClass::Register,
                            qualifiers: Qualifiers::NONE,
                            ctype: ctype.clone(),
                        },
                    );
                }
            }
            _ => unreachable!(),
        }
        Ok(ctype)
    }
    /* rewritten grammar:
    struct_declaration: (type_specifier | type_qualifier)+ struct_declarator_list ';' ;
    */
    fn struct_declaration(
        &mut self,
        ident: Option<InternedStr>,
        c_struct: bool,
        location: &Location,
    ) -> Result<Type, SyntaxError> {
        use std::rc::Rc;
        let mut members = vec![];
        loop {
            if let Some(Token::RightBrace) = self.peek_token() {
                break;
            } else if let Some(token) = self.match_next(&Token::Semicolon) {
                crate::utils::warn(
                    "extraneous semicolon in struct declaration is not allowed by ISO C",
                    token.location,
                );
                continue;
            } else {
                self.struct_declarator_list(&mut members)?;
            }
        }
        if members.is_empty() {
            let loc = self.next_location();
            self.semantic_err("cannot have empty struct", loc);
        }
        let constructor = if c_struct { Type::Struct } else { Type::Union };
        if let Some(id) = ident {
            let struct_ref = if let Some(TagEntry::Struct(struct_ref))
            | Some(TagEntry::Union(struct_ref)) =
                self.tag_scope.get_immediate(&id)
            {
                let struct_ref = *struct_ref;
                if !struct_ref.get().is_empty() {
                    self.semantic_err(
                        format!(
                            "redefinition of {} '{}'",
                            if c_struct { "struct" } else { "union" },
                            id
                        ),
                        *location,
                    );
                }
                struct_ref
            } else {
                StructRef::new()
            };
            struct_ref.update(members);
            let entry = if c_struct {
                TagEntry::Struct
            } else {
                TagEntry::Union
            }(struct_ref);
            self.tag_scope.insert(id, entry);
            Ok(constructor(StructType::Named(id, struct_ref)))
        } else {
            Ok(constructor(StructType::Anonymous(Rc::new(members))))
        }
    }
    fn bitfield(&mut self) -> Result<SIZE_T, SyntaxError> {
        Ok(self.constant_expr()?.const_int().unwrap_or_else(|err| {
            self.error_handler.push_back(err);
            1
        }))
    }
    /*
    struct_declarator_list: struct_declarator (',' struct_declarator)* ;
    struct_declarator
        : declarator
        | ':' constant_expr  // bitfield, not supported
        | declarator ':' constant_expr
        ;
    */
    fn struct_declarator_list(&mut self, members: &mut Vec<Symbol>) -> Result<(), SyntaxError> {
        let (sc, qualifiers, original_ctype, _) = self.declaration_specifiers()?;
        if let Some(token) = self.match_next(&Token::Semicolon) {
            crate::utils::warn("declaration does not declare anything", token.location);
            return Ok(());
        }
        let mut last_location;
        loop {
            if let Some(token) = self.match_next(&Token::Colon) {
                self.bitfield()?;
                crate::utils::warn(
                    "padding bits in bitfields are not implemented and will be ignored",
                    token.location,
                );
                self.expect(Token::Semicolon)?;
                return Ok(()); // NOTE: does not give a 2nd error if sc was given
            }
            let decl = self.declarator(false, qualifiers)?.unwrap();
            let (declarator, ctype) = decl
                .parse_type(original_ctype.clone(), false, &self.last_location)
                .recover(&mut self.error_handler);
            // TODO: Declarator needs to be redesigned so there's only one unwrap
            let Locatable { data: id, location } = declarator.unwrap();
            let symbol = Symbol {
                storage_class: StorageClass::Auto,
                qualifiers,
                ctype,
                init: false,
                id,
            };
            if let Some(token) = self.match_next(&Token::Colon) {
                let bit_size = self.bitfield()?;
                let type_size = symbol.ctype.sizeof().unwrap_or(0);
                if bit_size == 0 {
                    let err = format!(
                        "C does not have zero-sized types. hint: omit the declarator {}",
                        symbol.id
                    );
                    self.semantic_err(err, self.last_location);
                } else if bit_size > type_size * u64::from(crate::arch::CHAR_BIT) {
                    let err = format!(
                        "cannot have bitfield {} with size {} larger than containing type {}",
                        symbol.id, bit_size, symbol.ctype
                    );
                    self.semantic_err(err, token.location);
                }
                crate::utils::warn(
                    "bitfields are not implemented and will be ignored",
                    token.location,
                );
            };
            match symbol.ctype {
                Type::Struct(StructType::Named(_, members))
                | Type::Union(StructType::Named(_, members))
                    if members.get().is_empty() =>
                {
                    self.semantic_err(
                        format!(
                            "cannot use type '{}' before it has been defined",
                            symbol.ctype
                        ),
                        location,
                    );
                }
                _ => members.push(symbol),
            }
            last_location = location;
            if self.match_next(&Token::Comma).is_none() {
                self.expect(Token::Semicolon)?;
                break;
            }
        }
        if let Some(class) = sc {
            let member = members
                .last()
                .expect("should have seen at least one declaration");
            self.semantic_err(
                format!(
                    "cannot specify storage class '{}' for struct member '{}'",
                    class, member.id,
                ),
                last_location,
            );
        }
        Ok(())
    }
    /*
     * function parameters
     * reference grammar:
     *
     *  parameter_type_list:
     *        parameter_list
     *      | parameter_list ',' ELLIPSIS
     *      ;
     *
     *  parameter_list:
     *        parameter_declaration
     *      | parameter_list ',' parameter_declaration
     *      ;
     *
     *  parameter_declaration:
     *        declaration_specifiers declarator
     *      | declaration_specifiers
     *      | declaration_specifiers abstract_declarator
     *      ;
     *
     */
    fn parameter_type_list(&mut self) -> Result<DeclaratorType, SyntaxError> {
        self.expect(Token::LeftParen)
            .expect("parameter_type_list should only be called with '(' as the next token");
        let mut params = vec![];
        if self.match_next(&Token::RightParen).is_some() {
            return Ok(DeclaratorType::Function(FunctionDeclarator {
                params,
                varargs: false,
            }));
        }
        loop {
            if let Some(locatable) = self.match_next(&Token::Ellipsis) {
                if params.is_empty() {
                    self.semantic_err(
                        "ISO C requires a parameter before '...'".to_string(),
                        locatable.location,
                    );
                }
                // TODO: have a better error message for `int f(int, ..., int);`
                self.expect(Token::RightParen)?;
                return Ok(DeclaratorType::Function(FunctionDeclarator {
                    params,
                    varargs: true,
                }));
            }
            let (sc, quals, param_type, _) = self.declaration_specifiers()?;
            // true: allow abstract_declarators
            let declarator = self.declarator(true, quals)?;
            if let Some(storage_class) = sc {
                self.semantic_err(
                    format!(
                        "cannot specify storage class '{}' for {}",
                        storage_class,
                        if let Some(ref decl) = declarator {
                            if let Some(ref name) = decl.id() {
                                format!("parameter {}", name.data)
                            } else {
                                "unnamed parameter".to_string()
                            }
                        } else {
                            "<parse-error>".to_string()
                        }
                    ),
                    self.last_location,
                );
            }
            if let Some(decl) = declarator {
                let (id, mut ctype) = decl
                    .parse_type(param_type, false, &self.last_location)
                    .recover(&mut self.error_handler);
                // int f(int a[]) is the same as int f(int *a)
                // TODO: parse int f(int a[static 5])
                if let Type::Array(to, _) = ctype {
                    ctype = Type::Pointer(to);
                }
                // I will probably regret this in the future
                // default() for String is "",
                // which can never be passed in by the lexer
                // this also makes checking if the parameter is abstract or not easy to check
                let Locatable { location, data } = id.unwrap_or(Locatable {
                    location: self.next_location(),
                    data: Default::default(),
                });
                if data != Default::default() && params.iter().any(|p| p.data.id == data) {
                    self.semantic_err(
                        format!(
                            "duplicate parameter name '{}' in function declaration",
                            data,
                        ),
                        location,
                    );
                }
                params.push(Locatable {
                    location,
                    data: Symbol {
                        id: data,
                        ctype,
                        qualifiers: quals,
                        storage_class: StorageClass::Auto,
                        init: true,
                    },
                });
            } else {
                if param_type == Type::Void && !params.is_empty() {
                    let loc = self.next_location();
                    self.semantic_err(
                        "void must be the first and only parameter if specified",
                        loc,
                    );
                    continue;
                }
                // abstract param
                params.push(Locatable {
                    location: self.next_location(),
                    data: Symbol {
                        id: Default::default(),
                        ctype: param_type,
                        qualifiers: quals,
                        storage_class: StorageClass::Auto,
                        init: true,
                    },
                });
            }
            if self.match_next(&Token::Comma).is_none() {
                self.expect(Token::RightParen)?;
                return Ok(DeclaratorType::Function(FunctionDeclarator {
                    params,
                    varargs: false,
                }));
            }
        }
    }
    /*
     * not in original reference, see comments to next function
     *
     * rewritten grammar:
     *   postfix_type:
     *        '[' ']'
     *      | '[' constant_expr ']'
     *      | '(' ')'
     *      | '(' parameter_type_list ')'
     *      | /* empty */
     *      ;
     */
    fn postfix_type(
        &mut self,
        mut prefix: Option<Declarator>,
        allow_abstract: bool,
        qualifiers: Qualifiers,
    ) -> Result<Option<Declarator>, SyntaxError> {
        // postfix
        while let Some(data) = self.peek_token() {
            prefix = match data {
                // Array; Specified in section 6.7.6.2 of the C11 spec
                Token::LeftBracket => {
                    self.expect(Token::LeftBracket).unwrap();
                    if self.match_next(&Token::RightBracket).is_some() {
                        Some(Declarator {
                            current: DeclaratorType::Array(ArrayType::Unbounded),
                            next: prefix.map(Box::new),
                        })
                    } else {
                        if let Some(keyword) = self.match_next(&Token::Keyword(Keyword::Static)) {
                            if allow_abstract {
                                // TODO: Add information for the compiler to know
                                // to warn if `NULL` is passed into the function
                            } else {
                                self.semantic_err("`static` keyword for array sizes is only allowed in function declarations", keyword.location);
                            }
                        }

                        let expr = self.constant_expr()?;
                        self.expect(Token::RightBracket)?;
                        let length = expr.const_int().unwrap_or_else(|err| {
                            self.error_handler.push_back(err);
                            1
                        });
                        Some(Declarator {
                            current: DeclaratorType::Array(ArrayType::Fixed(length)),
                            next: prefix.map(Box::new),
                        })
                    }
                }
                Token::LeftParen => Some(Declarator {
                    current: self.parameter_type_list()?,
                    next: prefix.map(Box::new),
                }),
                _ => break,
            };
        }

        if let Some(Declarator {
            current: DeclaratorType::Function(_),
            ..
        }) = prefix
        {
            // `inline` is allowed on function declarations
        } else if qualifiers.inline {
            self.semantic_err(
                "`inline` is only allowed on function declarations",
                self.last_location,
            );
        }

        Ok(prefix)
    }
    /*
     * Originally written as follows:
     * direct_declarator
     *  : identifier
     *  | '(' declarator ')'
     *  | direct_declarator '[' ']'
     *  | direct_declarator '[' constant_expr ']'
     *  | direct_declarator '(' ')'
     *  | direct_declarator '(' parameter_type_list ')'
     *  ;
     *
     * Additionally, we combine abstract_declarators, because most of the code is the same.
     * direct_abstract_declarator
     *  : '(' abstract_declarator ')'
     *  | '[' ']'
     *  | '[' constant_expr ']'
     *  | direct_abstract_declarator '[' ']'
     *  | direct_abstract_declarator '[' constant_expr ']'
     *  | '(' ')'
     *  | '(' parameter_type_list ')'
     *  | direct_abstract_declarator '(' ')'
     *  | direct_abstract_declarator '(' parameter_type_list ')'
     *  ;
     *
     * Because we can't handle left-recursion, we rewrite it as follows:
     * direct_abstract_declarator
     *   | identifier postfix_type*
     *   : '(' abstract_declarator ')' postfix_type*
     *   | postfix_type*  /* only for abstract_declarators */
     *   ;
     *
     * postfix_type:
     *   : '[' ']'
     *   | '[' constant_expr ']'
     *   | '(' ')'
     *   | '(' parameter_type_list ')'
     *   ;
     *
     *   How do we tell abstract_declarator and parameter_type_list apart?
     *   parameter_type_list starts with declaration specifiers, abstract_declarator doesn't:
     *   https://stackoverflow.com/questions/56410673/how-should-int-fint-be-parsed
     */
    fn direct_declarator(
        &mut self,
        allow_abstract: bool,
        qualifiers: Qualifiers,
    ) -> Result<Option<Declarator>, SyntaxError> {
        // we'll pass this to postfix_type in just a second
        // if None, we didn't find an ID
        // should only happen if allow_abstract is true
        let decl: Option<Declarator> = match self.peek_token() {
            Some(Token::Id(_)) => {
                let Locatable { data, location } = self.next_token().unwrap();
                match data {
                    Token::Id(id) => Some(Declarator {
                        current: DeclaratorType::Id(id, location),
                        next: None,
                    }),
                    _ => panic!("peek() should always return the same thing as next()"),
                }
            }
            // handled by postfix_type
            Some(Token::LeftBracket) if allow_abstract => None,
            Some(Token::LeftParen) => {
                // this is the reason we need to save next - otherwise we
                // consume LeftParen without postfix_type ever seeing it
                match self.peek_next_token() {
                    // parameter_type_list, leave it for postfix_type
                    // need to check allow_abstract because we haven't seen an ID at
                    // this point
                    Some(Token::Keyword(k)) if k.is_decl_specifier() && allow_abstract => None,
                    // abstract_declarator - could be an error,
                    // but if so we'll catch it later
                    _ => {
                        // the one we already matched
                        self.expect(Token::LeftParen)
                            .expect("peek_next_token should be accurate");
                        let declarator = self.declarator(allow_abstract, qualifiers)?;
                        self.expect(Token::RightParen)?;
                        declarator
                    }
                }
            }
            _ if allow_abstract => None,
            Some(x) => {
                let err = Err(Locatable {
                    data: format!("expected variable name or '(', got '{}'", x),
                    location: self.next_location(),
                }
                .into());
                self.panic();
                return err;
            }
            None => {
                return Err(Locatable {
                    location: self.next_location(),
                    data: "expected variable name or '(', got <end-of-of-file>".to_string(),
                }
                .into());
            }
        };

        self.postfix_type(decl, allow_abstract, qualifiers)
    }
    /* parse everything after declaration specifiers. can be called recursively
     * allow_abstract: whether to require identifiers in declarators.
     * NOTE: whenever allow_abstract is `false`,
     *  either an identifier or an error will be returned.
     * when allow_abstract is `true`, an identifier may or may not be returned.
     * reference grammar:
     *
     *  declarator
     *      : direct_declarator
     *      | pointer declarator
     *      ;
     *
     *  direct_declarator
     *      : identifier
     *      | '(' declarator ')'
     *      | direct_declarator '[' ']'
     *      | direct_declarator '[' constant_expr ']'
     *      | direct_declarator '(' parameter_type_list ')'
     *      | direct_declarator '(' ')'
     *      ;
     *
     *  pointer
     *      : '*' specifier_qualifier_list_opt
     *      | '&'   /* C++ only */
     *      ;
     *
     */
    fn declarator(
        &mut self,
        allow_abstract: bool,
        qualifiers: Qualifiers,
    ) -> Result<Option<Declarator>, SyntaxError> {
        if let Some(data) = self.peek_token() {
            match data {
                Token::Star => {
                    self.next_token();
                    let mut pointer_qualifiers = Qualifiers::NONE;
                    while let Some(Locatable {
                        location,
                        data: Token::Keyword(keyword),
                    }) = self.match_any(&[
                        &Token::Keyword(Keyword::Const),
                        &Token::Keyword(Keyword::Volatile),
                        &Token::Keyword(Keyword::Restrict),
                        &Token::Keyword(Keyword::Atomic),
                        &Token::Keyword(Keyword::ThreadLocal),
                    ]) {
                        if keyword == Keyword::Const {
                            if pointer_qualifiers.c_const {
                                warn("duplicate 'const' declaration specifier", location);
                            } else {
                                pointer_qualifiers.c_const = true;
                            }
                        } else if keyword == Keyword::Volatile {
                            if pointer_qualifiers.volatile {
                                warn("duplicate 'volatile' declaration specifier", location);
                            } else {
                                pointer_qualifiers.volatile = true;
                            }
                        } else {
                            warn(
                                &format!("qualifier '{}' has not yet been implemented", keyword),
                                location,
                            );
                        }
                    }
                    // TODO: this is wrong
                    // const int *i; declares a pointer to const data: the pointer can
                    // be modified but the data cannot.
                    // int *const i; declares a const pointer to data: the data can be
                    // modified but the pointer cannot.
                    // We have this backwards.
                    Ok(Some(Declarator {
                        current: DeclaratorType::Pointer(pointer_qualifiers),
                        next: self.declarator(allow_abstract, qualifiers)?.map(Box::new),
                    }))
                }
                _ => self.direct_declarator(allow_abstract, qualifiers),
            }
        } else {
            // this is useful for integration tests, even though there's no scenario
            // where a type followed by EOF is legal in a real program
            self.direct_declarator(allow_abstract, qualifiers)
        }
    }
    /// initializer
    ///     : assignment_expr
    ///     | '{' initializer_list ','? '}'
    ///     ;
    ///
    /// initializer_list
    ///     : initializer
    ///     | initializer_list ',' initializer
    ///     ;
    ///
    /// Rewritten as
    /// initializer: assignment_expr
    ///     | '{' initializer (',' initializer)* '}'
    fn initializer(&mut self, ctype: &Type) -> Result<Initializer, SyntaxError> {
        // initializer_list
        if self.match_next(&Token::LeftBrace).is_some() {
            let mut elements = vec![];
            if let Some(token) = self.match_next(&Token::RightBrace) {
                self.semantic_err("initializers cannot be empty", token.location);
            }
            while self.match_next(&Token::RightBrace).is_none() {
                let elem_type = ctype.type_at(elements.len()).unwrap_or_else(|err| {
                    let loc = self.next_location();
                    self.semantic_err(err, loc);
                    Type::Error
                });
                elements.push(self.initializer(&elem_type)?);
                if self.match_next(&Token::RightBrace).is_some() {
                    break;
                }
                self.expect(Token::Comma)?;
            }
            return Ok(Initializer::InitializerList(elements));
        }
        let mut expr = self.assignment_expr()?;
        // The only time (that I know of) that an expression will initialize a non-scalar
        // is for character literals.
        let is_char_array = match ctype {
            Type::Array(inner, _) => inner.is_char(),
            _ => false,
        };
        // See section 6.7.9 of the C11 standard:
        // The initializer for a scalar shall be a single expression, optionally enclosed in braces.
        // The initial value of the object is that of the expression (after conversion)
        if !is_char_array {
            expr = expr
                .rval()
                // if ctype is not a scalar, this will report an error, so we don't have to handle it specially
                .cast(ctype)
                .recover(&mut self.error_handler);
        }
        if !expr.lval && self.scope.is_global() && ctype.is_pointer() {
            expr = Expr {
                lval: false,
                constexpr: false,
                location: expr.location,
                ctype: expr.ctype.clone(),
                expr: ExprType::StaticRef(Box::new(expr)),
            };
        }
        Ok(Initializer::Scalar(Box::new(expr)))
    }
    fn function_body(
        &mut self,
        id: InternedStr,
        ftype: FunctionType,
        location: Location,
    ) -> Result<Vec<Stmt>, SyntaxError> {
        // if it's a function, set up state so we know the return type
        // TODO: rework all of this so semantic analysis is done _after_ parsing
        // TODO: that will remove a lot of clones and also make the logic much simpler
        if self.current_function.is_some() {
            // TODO: allow function _declarations_ at local scope
            // e.g. int main() { int f(); return f(); }
            self.semantic_err(
                format!(
                    "functions cannot be nested. hint: try declaring {} as `static` at file scope",
                    id
                ),
                location,
            );
        }
        // add parameters to scope
        self.enter_scope();
        let len = ftype.params.len();
        for (i, param) in ftype.params.into_iter().enumerate() {
            if param.id == Default::default() {
                if param.ctype == Type::Void {
                    assert_eq!(len, 1);
                    break;
                }
                self.semantic_err(
                    format!(
                        "missing parameter name in function definition (parameter {} of type '{}')",
                        i, param.ctype
                    ),
                    location,
                );
            }
            self.scope.insert(param.id.clone(), param);
        }
        self.current_function = Some(FunctionData {
            return_type: *ftype.return_type,
            location,
            id,
        });

        // function body
        let body = match self.compound_statement() {
            Ok(Some(Stmt {
                data: StmtType::Compound(stmts),
                ..
            })) => Ok(stmts),
            Ok(None) => Ok(vec![]),
            Ok(x) => unreachable!(
                "expected compound_statement to return compound statement, got '{:#?}' instead",
                x
            ),
            Err(e) => Err(e),
        };
        self.current_function = None;
        self.leave_scope(self.last_location);
        body
    }
    #[inline]
    /* the reason this is such a mess (instead of just putting everything into
     * the hashmap, which would be much simpler logic) is so we have a Location
     * to go with every error
     * INVARIANT: keyword has not been seen before (i.e. not a duplicate)
     *
     * TODO: refactor this to use a HashSet<Locatable<Token>>
     */
    fn declaration_specifier(
        &mut self,
        keyword: Keyword,
        storage_class: &mut Option<StorageClass>,
        qualifiers: &mut Qualifiers,
        ctype: &mut Option<Type>,
        signed: &mut Option<bool>,
        location: Location,
    ) {
        // we use `if` instead of `qualifiers.x = keyword == y` because
        // we don't want to reset it if it's already true
        if keyword == Keyword::Const {
            qualifiers.c_const = true;
        } else if keyword == Keyword::Volatile {
            qualifiers.volatile = true;
        } else if keyword == Keyword::Inline {
            qualifiers.inline = true;
        } else if keyword == Keyword::Signed || keyword == Keyword::Unsigned {
            if *ctype == Some(Type::Float) || *ctype == Some(Type::Double) {
                self.semantic_err(
                    format!(
                        "invalid modifier '{}' for '{}'",
                        keyword,
                        ctype.as_ref().unwrap()
                    ),
                    location,
                );
            }
            if *signed == None {
                *signed = Some(keyword == Keyword::Signed);
            } else {
                self.semantic_err("types cannot be both signed and unsigned", location);
            }
        } else if let Ok(sc) = StorageClass::try_from(keyword) {
            if *storage_class == None {
                *storage_class = Some(sc);
            } else {
                self.semantic_err(
                    format!(
                        "multiple storage classes in declaration \
                         ('{}' and '{}')",
                        storage_class.unwrap(),
                        sc
                    ),
                    location,
                );
            }
        } else if keyword == Keyword::VaList {
            if let Some(ctype) = ctype {
                self.semantic_err(
                    format!(
                        "cannot combine '{}' with type '{}' in declaration",
                        keyword, ctype
                    ),
                    location,
                );
            } else {
                *ctype = Some(Type::VaList);
            }
        } else if keyword == Keyword::Float || keyword == Keyword::Double {
            if *signed != None {
                let s = if signed.unwrap() {
                    "signed"
                } else {
                    "unsigned"
                };
                self.semantic_err(
                    format!("invalid modifier '{}' for '{}'", s, keyword),
                    location,
                );
            } else {
                match ctype {
                    None => {}
                    Some(Type::Long(_)) if keyword == Keyword::Double => {}
                    Some(x) => self.semantic_err(
                        format!("cannot combine '{}' with '{}'", keyword, x),
                        location,
                    ),
                }
                *ctype = Some(Type::try_from(keyword).unwrap());
            }
        } else if keyword == Keyword::Void {
            match ctype {
                Some(x) => {
                    self.semantic_err(format!("cannot combine 'void' with '{}'", x), location)
                }
                None => *ctype = Some(Type::Void),
            }
        // if we get this far, keyword is an int type (char - long)
        } else if keyword == Keyword::Int {
            match ctype {
                Some(Type::Char(_)) | Some(Type::Short(_)) | Some(Type::Long(_))
                | Some(Type::Int(_)) => {}
                Some(x) => {
                    self.semantic_err(format!("cannot combine 'int' with '{}'", x), location)
                }
                None => *ctype = Some(Type::Int(true)),
            }
        } else {
            match ctype {
                None => {
                    *ctype = Some(Type::try_from(keyword).unwrap_or_else(|_| {
                        panic!("unrecognized declaration specifier {}", keyword)
                    }))
                }
                Some(x) => self.semantic_err(
                    format!("cannot combine '{}' modifier with type '{}'", keyword, x),
                    location,
                ),
            }
        }
    }
}

impl Keyword {
    fn is_qualifier(self) -> bool {
        self == Keyword::Const || self == Keyword::Volatile
    }
    fn is_storage_class(self) -> bool {
        StorageClass::try_from(self).is_ok()
    }
    pub fn is_decl_specifier(self) -> bool {
        use Keyword::*;
        match self {
            Unsigned | Signed | Bool | Char | Short | Int | Long | Float | Double | Void
            | Struct | Union | Enum | VaList | Complex | Imaginary | Extern | Static | Auto
            | Register | Typedef | Const | Volatile | Restrict | Atomic | ThreadLocal | Inline
            | NoReturn => true,
            _ => false,
        }
    }
}

impl TryFrom<Keyword> for Type {
    type Error = ();
    fn try_from(keyword: Keyword) -> Result<Type, ()> {
        use Type::*;
        match keyword {
            Keyword::Void => Ok(Void),
            Keyword::Bool => Ok(Bool),
            Keyword::Char => Ok(Char(true)),
            Keyword::Short => Ok(Short(true)),
            Keyword::Int => Ok(Int(true)),
            Keyword::Long => Ok(Long(true)),
            Keyword::Float => Ok(Float),
            Keyword::Double => Ok(Double),
            _ => Err(()),
        }
    }
}

impl Declarator {
    fn id(&self) -> Option<Locatable<InternedStr>> {
        match &self.current {
            DeclaratorType::Id(id, location) => Some(Locatable {
                data: *id,
                location: *location,
            }),
            _ => match &self.next {
                None => None,
                Some(x) => x.id(),
            },
        }
    }
    /// `current` should be only a base type, i.e. something returned by type_specifiers
    ///
    /// Explanation of the return type:
    /// `Option<Locatable<InternedStr>>`: the name of the declarator. May not exist for abstract parameters.
    /// `RecoverableResult<...>`: see documentation for why this exists
    fn parse_type(
        self,
        mut current: Type,
        is_typedef: bool,
        location: &Location, // only used for abstract parameters
    ) -> RecoverableResult<(Option<Locatable<InternedStr>>, Type), Vec<SemanticError>> {
        use DeclaratorType::*;
        let (mut declarator, mut identifier) = (Some(self), None);
        let mut pending_errs = vec![];
        while let Some(decl) = declarator {
            current = match decl.current {
                Id(id, location) => {
                    identifier = Some(Locatable { data: id, location });
                    current
                }
                Pointer(_) => Type::Pointer(Box::new(current)),
                Array(arr_type) => match current {
                    Type::Function(_) => {
                        let Locatable {
                            data: name,
                            location,
                        } = identifier.unwrap_or_else(|| Locatable {
                            location: *location,
                            data: InternedStr::get_or_intern("a"),
                        });
                        pending_errs.push(Locatable::new(
                            format!(
                                "array cannot contain function type '{}'. \
                                 help: try array of pointer to function: (*{}[])()",
                                current, name
                            ),
                            location,
                        ));
                        Type::Array(Box::new(current), arr_type)
                    }
                    _ => Type::Array(Box::new(current), arr_type),
                },
                Function(func_decl) => match current {
                    Type::Function(_) | Type::Array(_, _) => {
                        let func = mem::discriminant(&current)
                            == mem::discriminant(&Type::Function(FunctionType {
                                varargs: false,
                                return_type: Box::new(Type::Int(true)),
                                params: vec![],
                            }));
                        let Locatable {
                            data: name,
                            location,
                        } = identifier.unwrap_or_else(|| Locatable {
                            location: *location,
                            data: InternedStr::get_or_intern("f"),
                        });
                        let (typename, help) = if func {
                            ("function", format!("(*{}())()", name))
                        } else {
                            ("array", format!("*{}()", name))
                        };
                        pending_errs.push(Locatable {
                            data: format!(
                                "functions cannot return {} type '{}'. \
                                 help: try returning a pointer instead: {}",
                                typename, current, help,
                            ),
                            location,
                        });
                        Type::Function(FunctionType {
                            return_type: Box::new(current),
                            params: func_decl.params.into_iter().map(|x| x.data).collect(),
                            varargs: func_decl.varargs,
                        })
                    }
                    _ => Type::Function(FunctionType {
                        return_type: Box::new(current),
                        params: func_decl.params.into_iter().map(|x| x.data).collect(),
                        varargs: func_decl.varargs,
                    }),
                },
            };
            declarator = decl.next.map(|x| *x);
        }
        if current == Type::Void && !is_typedef {
            pending_errs.push(Locatable {
                data: "variables cannot have type 'void'".to_string(),
                location: identifier.map_or_else(|| *location, |l| l.location),
            });
        }
        if pending_errs.is_empty() {
            Ok((identifier, current))
        } else {
            Err((pending_errs, (identifier, current)))
        }
    }
}

impl Type {
    fn type_at(&self, index: usize) -> Result<Type, String> {
        match self {
            ty if ty.is_scalar() => {
                if index == 0 {
                    Ok(ty.clone())
                } else {
                    Err(format!(
                        "scalar initializers for '{}' may only have one element (initialized with {})",
                        ty, index + 1
                    ))
                }
            }
            Type::Array(inner, _) => Ok((**inner).clone()),
            Type::Struct(struct_type) => {
                let symbols = struct_type.members();
                symbols.get(index).map_or_else(
                    || {
                        Err(format!(
                            "too many initializers for struct (declared with {} elements, found {}",
                            symbols.len(),
                            index
                        ))
                    },
                    |symbol| Ok(symbol.ctype.clone()),
                )
            }
            Type::Union(struct_type) => {
                if index != 0 {
                    return Err("can only initialize first member of an enum".into());
                }
                let members = struct_type.members();
                Ok(members
                    .first()
                    .map(|m| m.ctype.clone())
                    .unwrap_or(Type::Error))
            }
            _ => unimplemented!("type checking for aggregate initializers of type {}", self),
        }
    }
}

#[derive(Clone, Debug)]
enum DeclaratorType {
    Id(InternedStr, Location),
    Pointer(Qualifiers),
    Array(ArrayType),
    Function(FunctionDeclarator),
    // enums, unions, structs, and typedefs can't appear in declarators
}

#[derive(Clone, Debug)]
struct FunctionDeclarator {
    params: Vec<Locatable<Symbol>>,
    varargs: bool,
}

#[derive(Clone, Debug)]
struct Declarator {
    current: DeclaratorType,
    next: Option<Box<Declarator>>,
}

#[cfg(test)]
mod tests {
    use crate::data::{
        prelude::*,
        types::{ArrayType, FunctionType},
        Declaration, Initializer, Qualifiers, Symbol,
    };
    use crate::intern::InternedStr;
    use crate::parse::tests::{match_all, match_data, parse, parse_all, ParseType};
    use std::boxed::Box;
    use Type::*;

    fn match_type(lexed: Option<ParseType>, given_type: Type) -> bool {
        match_data(lexed, |data| data.symbol.ctype == given_type)
    }
    #[test]
    fn test_decl_specifiers() {
        assert!(match_type(parse("char i;"), Type::Char(true)));
        assert!(match_type(parse("unsigned char i;"), Type::Char(false)));
        assert!(match_type(parse("signed short i;"), Type::Short(true)));
        assert!(match_type(parse("unsigned short i;"), Type::Short(false)));
        assert!(match_type(parse("long i;"), Type::Long(true)));
        assert!(match_type(parse("long long i;"), Type::Long(true)));
        assert!(match_type(parse("long unsigned i;"), Type::Long(false)));
        assert!(match_type(parse("int i;"), Type::Int(true)));
        assert!(match_type(parse("signed i;"), Type::Int(true)));
        assert!(match_type(parse("unsigned i;"), Type::Int(false)));
        assert!(match_type(parse("float f;"), Type::Float));
        assert!(match_type(parse("double d;"), Type::Double));
        assert!(match_type(parse("long double d;"), Type::Double));
        assert!(match_type(
            parse("void f();"),
            Type::Function(FunctionType {
                return_type: Box::new(Type::Void),
                params: vec![],
                varargs: false
            })
        ));
        assert!(match_type(parse("const volatile int f;"), Type::Int(true)));
    }
    #[test]
    fn test_bad_decl_specs() {
        assert!(parse("int;").is_none());
        assert!(parse("char char i;").unwrap().is_err());
        assert!(parse("char long i;").unwrap().is_err());
        assert!(parse("long char i;").unwrap().is_err());
        assert!(parse("float char i;").unwrap().is_err());
        assert!(parse("float double i;").unwrap().is_err());
        assert!(parse("double double i;").unwrap().is_err());
        assert!(parse("double unsigned i;").unwrap().is_err());
        assert!(parse("short double i;").unwrap().is_err());
        assert!(parse("int void i;").unwrap().is_err());
        assert!(parse("void int i;").unwrap().is_err());
        // default to int if we don't have a type
        // don't panic if we see duplicate specifiers
        assert!(match_type(parse("unsigned unsigned i;"), Type::Int(false)));
        assert!(match_type(parse("extern extern i;"), Type::Int(true)));
        assert!(match_type(parse("const const i;"), Type::Int(true)));
        assert!(match_type(parse("const volatile i;"), Type::Int(true)));
    }
    #[test]
    fn test_arrays() {
        assert!(match_type(
            parse("int a[];"),
            Array(Box::new(Int(true)), ArrayType::Unbounded)
        ));
        assert!(match_type(
            parse("unsigned a[];"),
            Array(Box::new(Int(false)), ArrayType::Unbounded)
        ));
        assert!(match_type(
            parse("_Bool a[][][];"),
            Array(
                Box::new(Array(
                    Box::new(Array(Box::new(Bool), ArrayType::Unbounded)),
                    ArrayType::Unbounded
                )),
                ArrayType::Unbounded
            )
        ));
    }
    #[test]
    fn test_pointers() {
        assert!(match_type(parse("void *a;"), Pointer(Box::new(Void))));
        assert!(match_type(
            parse("float *const a;"),
            Pointer(Box::new(Float))
        ));
        // cdecl: declare a as const pointer to volatile pointer to double
        assert!(match_type(
            parse("double *volatile *const a;"),
            Pointer(Box::new(Pointer(Box::new(Double))),)
        ));
        assert!(match_type(
            parse("_Bool *volatile const a;"),
            Pointer(Box::new(Bool)),
        ));
        assert!(match_type(
            parse("char (*(*f));"),
            Pointer(Box::new(Pointer(Box::new(Char(true)))))
        ));
    }
    #[test]
    fn test_pointers_and_arrays() {
        // cdecl: declare foo as array 10 of pointer to pointer to char
        assert!(match_type(
            parse("char **foo[10];"),
            Array(
                Box::new(Pointer(Box::new(Pointer(Box::new(Char(true)))))),
                ArrayType::Fixed(10),
            )
        ));
        // cdecl: declare foo as pointer to pointer to array 10 of int
        assert!(match_type(
            parse("int (**foo)[10];"),
            Pointer(Box::new(Pointer(Box::new(Array(
                Box::new(Int(true)),
                ArrayType::Fixed(10)
            )))),)
        ));
    }
    #[test]
    fn test_functions() {
        assert!(match_type(
            parse("void *f();"),
            Function(FunctionType {
                return_type: Box::new(Pointer(Box::new(Type::Void))),
                params: vec![],
                varargs: false,
            })
        ));
        // cdecl: declare i as pointer to function returning int;
        assert!(match_type(
            parse("int (*i)();"),
            Pointer(Box::new(Function(FunctionType {
                return_type: Box::new(Int(true)),
                params: vec![],
                varargs: false,
            })),)
        ));
        // cdecl: declare i as pointer to function (int, char, float) returning int
        assert!(match_type(
            parse("int (*i)(int, char, float);"),
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
            parse("int (*i)(int (*f)());"),
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
            parse("int f(int, ...);"),
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
            parse("void f(int a[static 5]);"),
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

        assert!(parse("int b[static 10];").unwrap().is_err());
    }
    #[test]
    fn test_inline_keyword() {
        // Correct usage
        assert!(match_type(
            parse("inline void f(void);"),
            Function(FunctionType {
                return_type: Box::new(Void),
                params: vec![],
                varargs: false,
            })
        ));

        // `inline` is not allowed in the following cases
        assert!(parse("inline int a;").unwrap().is_err()); // Normal declarations
        assert!(parse("void f(inline int a);").unwrap().is_err()); // Parameter lists
        assert!(parse("struct F { inline int a; } f;").unwrap().is_err()); // Struct members
        assert!(
            parse("int main() { char a = (inline char)(4); }") // Type names
                .unwrap()
                .is_err()
        );
        assert!(parse("typedef a inline int;").unwrap().is_err());
    }
    #[test]
    fn test_complex() {
        // cdecl: declare bar as const pointer to array 10 of pointer to function (int) returning const pointer to char
        assert!(match_type(
            parse("char * const (*(* const bar)[])(int );"),
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
            parse("int (*(*foo)(void))[];"),
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
            parse("const int (* volatile bar)[];"),
            Pointer(Box::new(Array(Box::new(Int(true)), ArrayType::Unbounded)),)
        ));
        // cdecl: declare x as function returning pointer to array 5 of pointer to function returning char
        assert!(match_type(
            parse("char (*(*x())[])();"),
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
        assert!(parse("int").unwrap().is_err());
        assert!(parse("int i").unwrap().is_err());
        // type error: cannot have array of functions or function returning array
        assert!(parse("int f()[];").unwrap().is_err());
        assert!(parse("int f[]();").unwrap().is_err());
        assert!(parse("int f()();").unwrap().is_err());
        assert!(parse("int (*f)[;").unwrap().is_err());
        // duplicate parameter name
        assert!(parse("int f(int a, int a);").unwrap().is_err());
    }
    #[test]
    fn test_initializers() {
        // scalars
        assert!(parse("int i = 3;").unwrap().is_ok());

        // bounded and unbounded arrays
        assert!(all_match!(
            Some(Ok(Locatable {
                data:
                    Declaration {
                        init: Some(Initializer::InitializerList(_)),
                        ..
                    },
                ..
            })),
            parse("int a[] = {1, 2, 3};"),
            parse("int a[3] = {1, 2, 3};"),
            // possibly with trailing commas
            parse("int a[] = {1, 2, 3,};"),
            parse("int a[3] = {1, 2, 3,};")
        ));
    }
    #[test]
    fn enum_declaration() {
        assert!(parse("enum;").unwrap().is_err());
        assert!(parse("enum e;").unwrap().is_err());
        assert!(parse("enum e {};").unwrap().is_err());
        assert!(parse("enum e { A }").unwrap().is_err());
        assert!(parse("enum { A };").is_none());
        assert!(match_type(
            parse("enum { A } E;"),
            Type::Enum(None, vec![("A".into(), 0)])
        ));
        assert!(match_type(
            parse("enum e { A = 1, B } E;"),
            Type::Enum(Some("e".into()), vec![("A".into(), 1), ("B".into(), 2)])
        ));
        assert!(match_type(
            parse("enum { A = -5, B, C = 2, D } E;"),
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
        assert!(dbg!(parse("struct { int:5; } a;")).unwrap().is_err());
        assert!(parse("struct { int a:5; } b;").unwrap().is_ok());
        assert!(parse("struct { int a:5, b:6; } c;").unwrap().is_ok());
        assert!(parse("struct { extern int a:5; } d;").unwrap().is_err());
    }
}
