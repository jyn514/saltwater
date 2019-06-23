use std::collections::{HashSet, VecDeque};
use std::convert::TryFrom;
use std::iter::Iterator;

use super::{Lexeme, Parser};
use crate::data::{
    ArrayType, Expr, FunctionType, Keyword, Locatable, Location, Qualifiers, Stmt, StorageClass,
    Symbol, Token, Type,
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

    /* NOTE: there's some fishiness here. Declarations can have multiple variables,
     * but we typed them as only having one Symbol. Wat do?
     * We push all but one declaration into the 'pending' vector
     * and return the last.
     */
    pub fn declaration(&mut self, start: Keyword) -> Option<Locatable<Result<Stmt, String>>> {
        let (sc, qualifiers, ctype) = match self.declaration_specifiers(start) {
            Ok(tuple) => tuple,
            Err(err) => {
                return Some(Locatable {
                    data: Err(err.data),
                    location: err.location,
                });
            }
        };
        while self.match_next(Token::Semicolon).is_none() {
            // declarator: Result<Declarator, Locatable<String>>
            match self.declarator(false) {
                Ok(Some(decl)) => {
                    let (id, ctype) = match decl
                        .parse_type(ctype.clone(), &self.last_location.as_ref().unwrap())
                    {
                        Err(err) => {
                            return Some(Locatable {
                                location: err.location,
                                data: Err(err.data),
                            })
                        }
                        Ok((id, ctype)) => (id, ctype),
                    };
                    let Locatable { location, data } = id.unwrap();
                    self.pending.push_back(Locatable {
                        location,
                        data: Ok(Stmt::Declaration(Symbol {
                            storage_class: sc,
                            qualifiers: qualifiers.clone(),
                            ctype,
                            id: data,
                        })),
                    });
                }
                Ok(None) => panic!(
                    "declarator should never return None when called with allow_abstract: false"
                ),
                Err(err) => {
                    self.pending.push_back(Locatable {
                        location: err.location,
                        data: Err(err.data),
                    });
                }
            }
            if self.match_next(Token::Comma).is_none() {
                self.expect(Token::Semicolon);
                break;
            }
        }
        // this is empty when we had specifiers without identifiers
        // e.g. `int;`
        self.pending.pop_front().or_else(|| {
            warn(
                "declaration does not declare anything",
                self.next_location(),
            );
            self.next()
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
        start: Keyword,
    ) -> Result<(StorageClass, Qualifiers, Type), Locatable<String>> {
        // TODO: initialization is a mess
        let mut keywords = HashSet::new();
        keywords.insert(start);
        let mut storage_class = StorageClass::try_from(start).ok();
        let mut qualifiers = Qualifiers {
            c_const: start == Keyword::Const,
            volatile: start == Keyword::Volatile,
        };
        let mut ctype = Type::try_from(start).ok();
        let mut signed = if start == Keyword::Signed {
            Some(true)
        } else if start == Keyword::Unsigned {
            Some(false)
        } else {
            None
        };
        let mut errors = vec![];
        // unsigned const int
        while let Some(Token::Keyword(keyword)) = self.peek_token() {
            if !keyword.is_decl_specifier() {
                break;
            }
            let Locatable {
                location,
                data: keyword,
            } = self.next_token().unwrap();
            let keyword = Self::expect_keyword(keyword);
            if keywords.insert(keyword) {
                declaration_specifier(
                    keyword,
                    &mut storage_class,
                    &mut qualifiers,
                    &mut ctype,
                    &mut signed,
                    &mut errors,
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
                        &location,
                    );
                // what is `short short` supposed to be?
                } else if keyword != Keyword::Long {
                    errors.push(Locatable {
                        data: format!("duplicate basic type '{}' in declarator", keyword),
                        location,
                    });
                }
            }
        }
        while errors.len() > 1 {
            let current = errors.pop().unwrap();
            self.pending.push_front(Locatable {
                location: current.location,
                data: Err(current.data),
            });
        }
        if !errors.is_empty() {
            return Err(errors.pop().unwrap());
        }
        let ctype = match ctype {
            Some(Type::Char(ref mut s))
            | Some(Type::Short(ref mut s))
            | Some(Type::Int(ref mut s))
            | Some(Type::Long(ref mut s)) => {
                *s = signed.unwrap_or(true);
                ctype.unwrap()
            }
            Some(_) => ctype.unwrap(),
            None => {
                if signed.is_none() {
                    warn(
                        "type specifier missing, defaults to int",
                        self.next_location(),
                    );
                }
                Type::Int(signed.unwrap_or(true))
            }
        };
        Ok((
            storage_class.unwrap_or(StorageClass::Auto),
            qualifiers,
            ctype,
        ))
    }
    /*
     * function parameters
     * reference grammar:
     *
     *  parameter_type_list:
     *        parameter_list
     *      | parameter_list ',' ELIPSIS
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
    fn parameter_type_list(&mut self) -> Result<DeclaratorType, Locatable<String>> {
        self.expect(Token::LeftParen);
        let mut params = vec![];
        let mut errs = VecDeque::new();
        if self.match_next(Token::RightParen).is_some() {
            return Ok(DeclaratorType::Function(FunctionDeclarator {
                params,
                varargs: false,
            }));
        }
        loop {
            if let Some(locatable) = self.match_next(Token::Ellipsis) {
                if params.is_empty() {
                    errs.push_back(Locatable {
                        location: locatable.location,
                        data: Err("ISO C requires a parameter before '...'".to_string()),
                    });
                }
                // TODO: have a better error message for `int f(int, ..., int);`
                self.expect(Token::RightParen);
                return Ok(DeclaratorType::Function(FunctionDeclarator {
                    params,
                    varargs: true,
                }));
            }
            let (start, location) = match self.peek_token() {
                Some(Token::Keyword(k)) if k.is_decl_specifier() => {
                    let next = self.next_token().unwrap();
                    (Self::expect_keyword(next.data), next.location)
                }
                _ => {
                    errs.push_back(Locatable {
                        location: self.next_location().clone(),
                        data: Err("function parameters require types".to_string()),
                    });
                    (Keyword::Int, self.next_location().clone())
                }
            };
            // TODO: handle errors
            let (sc, quals, param_type) = self.declaration_specifiers(start).unwrap_or((
                Default::default(),
                Default::default(),
                Type::Int(true),
            ));
            // true: allow abstract_declarators
            let declarator = match self.declarator(true) {
                Err(Locatable { location, data }) => {
                    errs.push_back(Locatable {
                        location,
                        data: Err(data),
                    });
                    continue;
                }
                Ok(declarator) => declarator,
            };
            // NOTE: we are more liberal here than gcc or clang,
            // we allow `int f(auto int);`
            if sc != StorageClass::Auto {
                errs.push_back(Locatable {
                    location, // TODO: use the location of 'start',
                    data: Err(format!(
                        "cannot specify storage class '{}' for {}",
                        sc,
                        if let Some(decl) = declarator {
                            if let Some(ref name) = decl.id() {
                                format!("parameter {}", name.data)
                            } else {
                                "unnamed parameter".to_string()
                            }
                        } else {
                            "<parse-error>".to_string()
                        }
                    )),
                });
            } else if let Some(decl) = declarator {
                let (id, ctype) = decl.parse_type(
                    param_type,
                    &self
                        .last_location
                        .as_ref()
                        .expect("If we see a token, there should be at least one stored locaiton"),
                )?;
                // I will probably regret this in the future
                // default() for String is "",
                // which can never be passed in by the lexer
                // this also makes checking if the parameter is abstract or not easy to check
                let Locatable { location, data } = id.unwrap_or(Locatable {
                    location: self.next_location().clone(),
                    data: Default::default(),
                });
                params.push(Locatable {
                    location,
                    data: Symbol {
                        id: data,
                        ctype,
                        qualifiers: quals,
                        storage_class: StorageClass::Auto,
                    },
                });
            } else {
                // abstract param
                params.push(Locatable {
                    location: self.next_location().clone(),
                    data: Symbol {
                        id: Default::default(),
                        ctype: param_type,
                        qualifiers: quals,
                        storage_class: StorageClass::Auto,
                    },
                });
            }
            if self.match_next(Token::Comma).is_none() {
                self.expect(Token::RightParen);
                // TODO: handle errors (what should the return type be?)
                //let err = errs.pop_front();
                self.pending.append(&mut errs);
                //err.unwrap_or(
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
    ) -> Result<Option<Declarator>, Locatable<String>> {
        // postfix
        while let Some(data) = self.peek_token() {
            prefix = match data {
                // array
                Token::LeftBracket => {
                    self.expect(Token::LeftBracket);
                    if self.match_next(Token::RightBracket).is_some() {
                        Some(Declarator {
                            current: DeclaratorType::Array(ArrayType::Unbounded),
                            next: prefix.map(Box::new),
                        })
                    } else {
                        let expr = self.parse_expr();
                        self.expect(Token::RightBracket);
                        Some(Declarator {
                            current: DeclaratorType::Array(ArrayType::Fixed(Box::new(expr))),
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
    ) -> Result<Option<Declarator>, Locatable<String>> {
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
                        self.expect(Token::LeftParen);
                        let declarator = self.declarator(allow_abstract)?;
                        self.expect(Token::RightParen);
                        declarator
                    }
                }
            }
            _ if allow_abstract => None,
            Some(x) => {
                return Err(Locatable {
                    data: format!("expected identifier or '(', got '{}'", x),
                    location: self.next_location().clone(),
                })
            }
            None => {
                return Err(Locatable {
                    location: self.next_location().clone(),
                    data: "expected identifier or '(', got <end-of-of-file>".to_string(),
                })
            }
        };
        self.postfix_type(decl)
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
    ) -> Result<Option<Declarator>, Locatable<String>> {
        if let Some(data) = self.peek_token() {
            match data {
                Token::Star => {
                    self.next_token();
                    let mut qualifiers = Qualifiers::NONE;
                    while let Some(Locatable {
                        location,
                        data: Token::Keyword(keyword),
                    }) = self.match_any(&[
                        Token::Keyword(Keyword::Const),
                        Token::Keyword(Keyword::Volatile),
                    ]) {
                        if keyword == Keyword::Const {
                            if qualifiers.c_const {
                                warn("duplicate 'const' declaration specifier", &location);
                            } else {
                                qualifiers.c_const = true;
                            }
                        } else if keyword == Keyword::Volatile {
                            if qualifiers.volatile {
                                warn("duplicate 'volatile' declaration specifier", &location);
                            } else {
                                qualifiers.volatile = true;
                            }
                        }
                    }
                    Ok(Some(Declarator {
                        current: DeclaratorType::Pointer(qualifiers),
                        next: self.declarator(allow_abstract)?.map(Box::new),
                    }))
                }
                _ => self.direct_declarator(allow_abstract),
            }
        } else {
            Err(Locatable {
                location: self.next_location().clone(),
                data: "expected declarator, got <end-of-file>".to_string(),
            })
        }
    }
    fn parse_expr(&mut self) -> Expr {
        // TODO: oh honey
        self.next_token();
        Expr::Int(Token::Int(10))
    }
}

#[inline]
/* the reason this is such a mess (instead of just putting everything into
 * the hashmap, which would be much simpler logic) is so we have a Location
 * to go with every error
 * INVARIANT: keyword has not been seen before (i.e. not a duplicate)
 */
fn declaration_specifier(
    keyword: Keyword,
    storage_class: &mut Option<StorageClass>,
    qualifiers: &mut Qualifiers,
    ctype: &mut Option<Type>,
    signed: &mut Option<bool>,
    errors: &mut Vec<Locatable<String>>,
    location: Location,
) {
    // we use `if` instead of `qualifiers.x = keyword == y` because
    // we don't want to reset it if it's already true
    if keyword == Keyword::Const {
        qualifiers.c_const = true;
    } else if keyword == Keyword::Volatile {
        qualifiers.volatile = true;
    } else if keyword == Keyword::Signed || keyword == Keyword::Unsigned {
        if *ctype == Some(Type::Float) || *ctype == Some(Type::Double) {
            errors.push(Locatable {
                data: format!(
                    "invalid modifier '{}' for '{}'",
                    keyword,
                    ctype.as_ref().unwrap()
                ),
                location: location.clone(),
            });
        }
        if *signed == None {
            *signed = Some(keyword == Keyword::Signed);
        } else {
            errors.push(Locatable {
                data: "types cannot be both signed and unsigned".to_string(),
                location,
            });
        }
    } else if let Ok(sc) = StorageClass::try_from(keyword) {
        if *storage_class == None {
            *storage_class = Some(sc);
        } else {
            errors.push(Locatable {
                data: format!(
                    "multiple storage classes in declaration \
                     ('{}' and '{}')",
                    storage_class.unwrap(),
                    sc
                ),
                location,
            });
        }
    } else if keyword == Keyword::Float || keyword == Keyword::Double {
        if *signed != None {
            let s = if signed.unwrap() {
                "signed"
            } else {
                "unsigned"
            };
            errors.push(Locatable {
                data: format!("invalid modifier '{}' for '{}'", s, keyword),
                location,
            });
        } else {
            match ctype {
                None => {}
                Some(Type::Long(_)) if keyword == Keyword::Double => {}
                Some(x) => errors.push(Locatable {
                    data: format!("cannot combine '{}' with '{}'", keyword, x),
                    location,
                }),
            }
            *ctype = Some(Type::try_from(keyword).unwrap());
        }
    } else if keyword == Keyword::Void {
        match ctype {
            Some(x) => errors.push(Locatable {
                data: format!("cannot combine 'void' with '{}'", x),
                location,
            }),
            None => *ctype = Some(Type::Void),
        }
    // if we get this far, keyword is an int type (char - long)
    } else if keyword == Keyword::Int {
        match ctype {
            Some(Type::Char(_)) | Some(Type::Short(_)) | Some(Type::Long(_))
            | Some(Type::Int(_)) => {}
            Some(x) => errors.push(Locatable {
                data: format!("cannot combine 'int' with '{}'", x),
                location,
            }),
            None => *ctype = Some(Type::Int(true)),
        }
    } else {
        match ctype {
            None | Some(Type::Int(_)) => {
                *ctype = Some(
                    Type::try_from(keyword)
                        .expect("keyword should be an integer or integer modifier"),
                )
            }
            Some(x) => errors.push(Locatable {
                data: format!("cannot combine '{}' modifier with type '{}'", keyword, x),
                location,
            }),
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
            Unsigned | Signed | Void | Bool | Char | Short | Int | Long | Float | Double
            | Extern | Static | Auto | Register | Const | Volatile => true,
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
    fn id(&self) -> Option<Locatable<String>> {
        match &self.current {
            DeclaratorType::Id(id, location) => Some(Locatable {
                data: id.clone(),
                location: location.clone(),
            }),
            _ => match &self.next {
                None => None,
                Some(x) => x.id(),
            },
        }
    }
    // `current` should be only a base type, i.e. something returned by type_specifiers
    fn parse_type(
        self,
        mut current: Type,
        location: &Location, // only used for abstract parameters
    ) -> Result<(Option<Locatable<String>>, Type), Locatable<String>> {
        use DeclaratorType::*;
        // TODO(July 2019): make this one call when rust 1.36 comes out
        let mut declarator = Some(self);
        let mut identifier = None;
        while let Some(decl) = declarator {
            current = match decl.current {
                Id(id, location) => {
                    identifier = Some(Locatable { data: id, location });
                    current
                }
                Pointer(quals) => Type::Pointer(Box::new(current), quals),
                Array(arr_type) => match current {
                    Type::Function(_) => {
                        return Err(Locatable {
                            data: format!("array cannot contain function type '{}'", current),
                            location: identifier.map_or_else(|| location.clone(), |id| id.location),
                        });
                    }
                    _ => Type::Array(Box::new(current), arr_type),
                },
                Function(func_decl) => match current {
                    Type::Function(_) | Type::Array(_, _) => {
                        return Err(Locatable {
                            data: format!(
                                "functions cannot return function or array type '{}'",
                                current
                            ),
                            location: identifier.map_or_else(|| location.clone(), |id| id.location),
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
        Ok((identifier, current))
    }
}

#[derive(Clone, Debug)]
enum DeclaratorType {
    Id(String, Location),
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
        ArrayType, Expr, FunctionType, Qualifiers, Stmt, Symbol, Token,
        Type::{self, *},
    };
    use crate::parse::tests::{match_all, match_data, parse, parse_all, ParseType};
    use std::boxed::Box;

    fn match_type(lexed: Option<ParseType>, given_type: Type) -> bool {
        match_data(lexed, |data| match data {
            Ok(Stmt::Declaration(symbol)) => symbol.ctype == given_type,
            _ => false,
        })
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
        assert!(parse("char char i;").unwrap().data.is_err());
        assert!(parse("char long i;").unwrap().data.is_err());
        assert!(parse("long char i;").unwrap().data.is_err());
        assert!(parse("float char i;").unwrap().data.is_err());
        assert!(parse("float double i;").unwrap().data.is_err());
        assert!(parse("double double i;").unwrap().data.is_err());
        assert!(parse("double unsigned i;").unwrap().data.is_err());
        assert!(parse("short double i;").unwrap().data.is_err());
        assert!(parse("int void i;").unwrap().data.is_err());
        assert!(parse("void int i;").unwrap().data.is_err());
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
        assert!(match_type(
            parse("void *a;"),
            Pointer(Box::new(Void), Default::default())
        ));
        assert!(match_type(
            parse("float *const a;"),
            Pointer(Box::new(Float), Qualifiers::CONST)
        ));
        // cdecl: declare a as const pointer to volatile pointer to double
        assert!(match_type(
            parse("double *volatile *const a;"),
            Pointer(
                Box::new(Pointer(Box::new(Double), Qualifiers::VOLATILE)),
                Qualifiers::CONST
            )
        ));
        assert!(match_type(
            parse("_Bool *volatile const a;"),
            Pointer(Box::new(Bool), Qualifiers::CONST_VOLATILE)
        ));
        assert!(match_type(
            parse("char (*(*f));"),
            Pointer(
                Box::new(Pointer(Box::new(Char(true)), Qualifiers::NONE)),
                Qualifiers::NONE
            )
        ));
    }
    #[test]
    fn test_pointers_and_arrays() {
        // cdecl: declare foo as array 10 of pointer to pointer to char
        assert!(match_type(
            parse("char **foo[10];"),
            Array(
                Box::new(Pointer(
                    Box::new(Pointer(Box::new(Char(true)), Default::default(),)),
                    Default::default()
                )),
                ArrayType::Fixed(Box::new(Expr::Int(Token::Int(10))))
            )
        ));
        // cdecl: declare foo as pointer to pointer to array 10 of int
        assert!(match_type(
            parse("int (**foo)[10];"),
            Pointer(
                Box::new(Pointer(
                    Box::new(Array(
                        Box::new(Int(true)),
                        ArrayType::Fixed(Box::new(Expr::Int(Token::Int(10))))
                    )),
                    Default::default()
                )),
                Default::default()
            )
        ));
    }
    #[test]
    fn test_functions() {
        // cdecl: declare i as pointer to function returning int;
        assert!(match_type(
            parse("int (*i)();"),
            Pointer(
                Box::new(Function(FunctionType {
                    return_type: Box::new(Int(true)),
                    params: vec![],
                    varargs: false,
                })),
                Qualifiers::NONE
            )
        ));
        // cdecl: declare i as pointer to function (int, char, float) returning int
        assert!(match_type(
            parse("int (*i)(int, char, float);"),
            Pointer(
                Box::new(Function(FunctionType {
                    return_type: Box::new(Int(true)),
                    params: vec![
                        Symbol {
                            id: Default::default(),
                            ctype: Int(true),
                            qualifiers: Default::default(),
                            storage_class: Default::default()
                        },
                        Symbol {
                            id: Default::default(),
                            ctype: Char(true),
                            qualifiers: Default::default(),
                            storage_class: Default::default()
                        },
                        Symbol {
                            id: Default::default(),
                            ctype: Float,
                            qualifiers: Default::default(),
                            storage_class: Default::default()
                        }
                    ],
                    varargs: false,
                })),
                Qualifiers::NONE
            )
        ));
        // cdecl: declare i as pointer to function (pointer to function returning int) returning int
        assert!(match_type(
            parse("int (*i)(int (*f)());"),
            Pointer(
                Box::new(Function(FunctionType {
                    return_type: Box::new(Int(true)),
                    params: vec![Symbol {
                        id: "f".to_string(),
                        ctype: Pointer(
                            Box::new(Function(FunctionType {
                                return_type: Box::new(Int(true)),
                                params: vec![],
                                varargs: false
                            })),
                            Default::default()
                        ),
                        qualifiers: Default::default(),
                        storage_class: Default::default(),
                    }],
                    varargs: false,
                }),),
                Default::default()
            )
        ));
        assert!(match_type(
            parse("int f(int, ...);"),
            Function(FunctionType {
                return_type: Box::new(Int(true)),
                params: vec![Symbol {
                    id: Default::default(),
                    ctype: Int(true),
                    qualifiers: Default::default(),
                    storage_class: Default::default()
                }],
                varargs: true,
            })
        ));
    }
    #[test]
    fn test_complex() {
        // cdecl: declare bar as const pointer to array 10 of pointer to function (int) returning const pointer to char
        assert!(match_type(
            parse("char * const (*(* const bar)[10])(int );"),
            Pointer(
                Box::new(Array(
                    Box::new(Pointer(
                        Box::new(Function(FunctionType {
                            return_type: Box::new(Pointer(Box::new(Char(true)), Qualifiers::CONST)),
                            params: vec![Symbol {
                                ctype: Int(true),
                                storage_class: Default::default(),
                                id: String::new(),
                                qualifiers: Qualifiers::NONE,
                            }],
                            varargs: false,
                        })),
                        Qualifiers::NONE
                    )),
                    ArrayType::Fixed(Box::new(Expr::Int(Token::Int(10))))
                )),
                Qualifiers::CONST
            )
        ));
        // cdecl: declare foo as pointer to function (void) returning pointer to array 3 of int
        assert!(match_type(
            parse("int (*(*foo)(void))[10];"),
            Pointer(
                Box::new(Function(FunctionType {
                    return_type: Box::new(Pointer(
                        Box::new(Array(
                            Box::new(Int(true)),
                            ArrayType::Fixed(Box::new(Expr::Int(Token::Int(10))))
                        )),
                        Default::default()
                    )),
                    params: vec![Symbol {
                        ctype: Void,
                        storage_class: Default::default(),
                        id: Default::default(),
                        qualifiers: Default::default(),
                    }],
                    varargs: false,
                })),
                Default::default()
            )
        ));
        // cdecl: declare bar as volatile pointer to array 64 of const int
        assert!(match_type(
            parse("const int (* volatile bar)[];"),
            Pointer(
                Box::new(Array(Box::new(Int(true)), ArrayType::Unbounded)),
                Qualifiers::VOLATILE
            )
        ));
        // cdecl: declare x as function returning pointer to array 5 of pointer to function returning char
        assert!(match_type(
            parse("char (*(*x())[])();"),
            Function(FunctionType {
                return_type: Box::new(Pointer(
                    Box::new(Array(
                        Box::new(Pointer(
                            Box::new(Function(FunctionType {
                                return_type: Box::new(Char(true)),
                                params: vec![],
                                varargs: false,
                            })),
                            Default::default()
                        )),
                        ArrayType::Unbounded
                    )),
                    Default::default()
                )),
                params: vec![],
                varargs: false,
            })
        ));
    }
    #[test]
    fn test_multiple() {
        let parsed = parse_all("int i, j, k;");
        assert!(parsed.len() == 3);
        assert!(match_all(parsed.into_iter(), |i| match i {
            Ok(Stmt::Declaration(symbol)) => symbol.ctype == Type::Int(true),
            _ => false,
        }));
        let mut parsed = parse_all("char *p, c, **pp, f();");
        assert!(parsed.len() == 4);
        assert!(match_type(
            Some(parsed.remove(0)),
            Type::Pointer(Box::new(Type::Char(true)), Default::default())
        ));
        assert!(match_type(Some(parsed.remove(0)), Type::Char(true)));
        assert!(match_type(
            Some(parsed.remove(0)),
            Type::Pointer(
                Box::new(Type::Pointer(
                    Box::new(Type::Char(true)),
                    Default::default()
                )),
                Default::default()
            )
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
    fn test_decl_errors() {
        // no semicolon
        assert!(parse("int").unwrap().data.is_err());
        assert!(parse("int i").unwrap().data.is_err());
        // type error: cannot have array of functions or function returning array
        assert!(parse("int f()[];").unwrap().data.is_err());
        assert!(parse("int f[]();").unwrap().data.is_err());
        assert!(parse("int f()();").unwrap().data.is_err());
        // TODO: the error for this is wrong and will be until I implement parse_expr()
        assert!(parse("int (*f)[;").unwrap().data.is_err());
    }
}
