use std::collections::{HashSet, VecDeque};
use std::convert::TryFrom;
use std::iter::{Iterator, Peekable};
use std::mem;

use crate::data::{
    ArrayType, Expr, Keyword, Locatable, Location, Qualifiers, Stmt, StorageClass, Symbol, Token,
    Type,
};
use crate::utils::{error, warn};

type Lexeme = Locatable<Result<Token, String>>;

#[derive(Debug)]
pub struct Parser<I: Iterator<Item = Lexeme>> {
    tokens: Peekable<I>,
    pending: VecDeque<Locatable<Result<Stmt, String>>>,
    last_location: Option<Location>,
    current: Option<Locatable<Token>>,
}

impl<I> Parser<I>
where
    I: Iterator<Item = Lexeme>,
{
    pub fn new(iter: I) -> Self {
        Parser {
            tokens: iter.peekable(),
            pending: Default::default(),
            last_location: None,
            current: None,
        }
    }
}

impl<I: Iterator<Item = Lexeme>> Iterator for Parser<I> {
    type Item = Locatable<Result<Stmt, String>>;
    fn next(&mut self) -> Option<Self::Item> {
        self.pending.pop_front().or_else(|| {
            let Locatable {
                data: lexed,
                location,
            } = self.next_token()?;
            match lexed {
                // NOTE: we do not allow implicit int
                // https://stackoverflow.com/questions/11064292
                Token::Keyword(t) if t.is_decl_specifier() => self.parse_decl(t),
                _ => Some(Locatable {
                    data: Err("not handled".to_string()),
                    location,
                }),
            }
        })
    }
}
#[inline]
/* the reason this is such a mess (instead of just putting everything into
 * the hashmap, which would be much simpler logic) is so we have a Location
 * to go with every error */
fn handle_single_decl_specifier(
    keyword: Keyword,
    storage_class: &mut Option<StorageClass>,
    qualifiers: &mut Qualifiers,
    keywords: &mut HashSet<Keyword>,
    ctype: &mut Option<Type>,
    signed: &mut Option<bool>,
    errors: &mut Vec<Locatable<String>>,
    location: Location,
) {
    if !keywords.insert(keyword) {
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
                location: location.clone(),
            });
        }
        return;
    }
    // we use `if` instead of `qualifiers.x = keyword == y` because
    // we don't want to reset it if it's already true
    if keyword == Keyword::Const {
        qualifiers.c_const = true;
    } else if keyword == Keyword::Volatile {
        qualifiers.volatile = true;
    } else if keyword == Keyword::Signed || keyword == Keyword::Unsigned {
        if *ctype == Some(Type::Float) || *ctype == Some(Type::Double) {
            errors.push(Locatable {
                data: "double or float cannot be signed or unsigned".to_string(),
                location: location.clone(),
            });
        }
        if *signed == None {
            *signed = Some(keyword == Keyword::Signed);
        } else if signed.unwrap() != (keyword == Keyword::Signed) {
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
        } else if keyword == Keyword::Float {
            match ctype {
                Some(x) => errors.push(Locatable {
                    data: format!("cannot combine 'float' with '{}'", x),
                    location,
                }),
                None => {}
            }
            *ctype = Some(Type::Float);
        } else {
            match ctype {
                None | Some(Type::Long(_)) => {}
                Some(x) => errors.push(Locatable {
                    data: format!("cannot combine 'double' with '{}'", x),
                    location,
                }),
            }
            *ctype = Some(Type::Double);
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

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    fn next_token(&mut self) -> Option<Locatable<Token>> {
        if self.current.is_some() {
            mem::replace(&mut self.current, None)
        } else {
            match self.tokens.next() {
                Some(Locatable {
                    data: Ok(token),
                    location,
                }) => {
                    self.last_location = Some(location.clone());
                    Some(Locatable {
                        data: token,
                        location,
                    })
                }
                None => None,
                Some(Locatable {
                    data: Err(err),
                    location,
                }) => {
                    error(&err, &location);
                    self.last_location = Some(location);
                    self.next_token()
                }
            }
        }
    }
    fn peek_token(&mut self) -> Option<&Locatable<Token>> {
        if self.current.is_none() {
            self.current = self.next_token();
        }
        self.current.as_ref()
    }
    fn next_location(&mut self) -> &Location {
        if self.peek_token().is_some() {
            &self.peek_token().unwrap().location
        } else {
            self.last_location
                .as_ref()
                .expect("can't call next_location on an empty file")
        }
    }
    fn match_next(&mut self, next: Token) -> Option<Locatable<Token>> {
        self.match_any(&[next])
    }
    fn match_any(&mut self, choices: &[Token]) -> Option<Locatable<Token>> {
        match self.peek_token() {
            Some(Locatable { data, .. }) => {
                for token in choices {
                    if token == data {
                        return self.next_token();
                    }
                }
                None
            }
            _ => None,
        }
    }
    fn expect(&mut self, next: Token) -> (bool, &Location) {
        match self.peek_token() {
            Some(Locatable { data, .. }) if *data == next => {
                self.next_token();
                (
                    true,
                    self.last_location
                        .as_ref()
                        .expect("last_location should be set whenever next_token is called"),
                )
            }
            Some(Locatable { location, data }) => {
                // since we're only peeking, we can't move the next token
                let (location, message) = (location.clone(), data.to_string());
                self.pending.push_back(Locatable {
                    location,
                    data: Err(format!("expected '{}', got '{}'", next, message)),
                });
                (false, self.next_location())
            }
            None => {
                let location = self
                    .last_location
                    .as_ref()
                    .expect("parser.expect cannot be called at start of program");
                self.pending.push_back(Locatable {
                    location: location.clone(),
                    data: Err(format!("expected '{}', got <end-of-file>", next)),
                });
                (false, location)
            }
        }
    }
    // this is an utter hack
    // NOTE: the reason the return type is so weird (Result<_, Locatable<_>)
    // is because declaration specifiers can never be a statement on their own:
    // the associated location always belongs to the identifier
    fn parse_decl_specifiers(
        &mut self,
        start: Keyword,
    ) -> Result<(StorageClass, Qualifiers, Type), Locatable<String>> {
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
        while let Some(locatable) = self.peek_token() {
            let keyword = match locatable.data {
                Token::Keyword(k) if k.is_decl_specifier() => k,
                _ => break,
            };
            let locatable = self.next_token().unwrap();
            handle_single_decl_specifier(
                keyword,
                &mut storage_class,
                &mut qualifiers,
                &mut keywords,
                &mut ctype,
                &mut signed,
                &mut errors,
                locatable.location,
            );
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
    /* parse everything after declaration specifiers. can be called recursively */
    fn parse_type(&mut self, ctype: &Type) -> Locatable<Result<(String, Type), String>> {
        if let Some(Locatable { data, location }) = self.peek_token() {
            let prefix = match data {
                Token::LeftParen => {
                    self.next_token();
                    let next = self.parse_type(ctype);
                    self.expect(Token::RightParen);
                    match next.data {
                        Ok(tuple) => Locatable {
                            location: next.location,
                            data: tuple,
                        },
                        Err(_) => return next,
                    }
                }
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
                    match self.parse_type(ctype) {
                        Locatable {
                            location,
                            data: Ok((id, ctype)),
                        } => Locatable {
                            location,
                            data: (id, Type::Pointer(Box::new(ctype), qualifiers)),
                        },
                        x => return x,
                    }
                }
                Token::Id(_) => {
                    let Locatable { location, data } = self.next_token().unwrap();
                    let id = match data {
                        Token::Id(id) => id,
                        _ => panic!("how could peek return something different from next?"),
                    };
                    Locatable {
                        location,
                        data: (id, ctype.clone()),
                    }
                }
                x => {
                    return Locatable {
                        location: location.clone(),
                        data: Err(format!("expected '(', '*', or identifier, got '{}'", x)),
                    }
                }
            };
            // postfix
            if let Some(Locatable { data, .. }) = self.peek_token() {
                let Locatable {
                    location,
                    data: (id, ctype),
                } = prefix;
                match data {
                    Token::LeftBracket => {
                        self.expect(Token::LeftBracket);
                        if self.match_next(Token::RightBracket).is_some() {
                            Locatable {
                                location,
                                data: Ok((id, Type::Array(Box::new(ctype), ArrayType::Unbounded))),
                            }
                        } else {
                            let expr = self.parse_expr();
                            self.expect(Token::RightBracket);
                            Locatable {
                                location,
                                data: Ok((
                                    id,
                                    Type::Array(Box::new(ctype), ArrayType::Fixed(Box::new(expr))),
                                )),
                            }
                        }
                    }
                    _ => Locatable {
                        data: Ok((id, ctype)),
                        location,
                    },
                }
            } else {
                Locatable {
                    location: prefix.location,
                    data: Ok(prefix.data),
                }
            }
        } else {
            Locatable {
                location: self.next_location().clone(),
                data: Err("expected type, got <end-of-file>".to_string()),
            }
        }
    }
    // NOTE: there's some fishiness here. Declarations can have multiple variables,
    // but we typed them as only having one Symbol. Wat do?
    // We push all but one declaration into the 'pending' vector
    // and return the last.
    fn parse_decl(&mut self, start: Keyword) -> Option<Locatable<Result<Stmt, String>>> {
        let (sc, qualifiers, ctype) = match self.parse_decl_specifiers(start) {
            Ok(tuple) => tuple,
            Err(err) => {
                return Some(Locatable {
                    data: Err(err.data),
                    location: err.location,
                });
            }
        };
        while self.match_next(Token::Semicolon).is_none() {
            let Locatable { location, data } = self.parse_type(&ctype);
            match data {
                Ok(decl) => {
                    self.pending.push_back(Locatable {
                        location,
                        data: Ok(Stmt::Declaration(Symbol {
                            storage_class: sc,
                            qualifiers: qualifiers.clone(),
                            c_type: decl.1,
                            id: decl.0,
                        })),
                    });
                }
                Err(err) => {
                    self.pending.push_back(Locatable {
                        location,
                        data: Err(err),
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
}

impl Keyword {
    fn is_qualifier(self) -> bool {
        self == Keyword::Const || self == Keyword::Volatile
    }
    fn is_storage_class(self) -> bool {
        StorageClass::try_from(self).is_ok()
    }
    fn is_decl_specifier(self) -> bool {
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

#[cfg(test)]
mod tests {
    use super::Parser;
    use crate::data::{Expr, Locatable, Stmt, Token, Type};
    use crate::Lexer;
    type ParseType = Locatable<Result<Stmt, String>>;
    fn parse(input: &str) -> Option<ParseType> {
        parse_all(input).get(0).cloned()
    }
    fn parse_all(input: &str) -> Vec<ParseType> {
        Parser::new(Lexer::new("<test suite>".to_string(), input.chars())).collect()
    }
    fn match_data<T>(lexed: Option<ParseType>, closure: T) -> bool
    where
        T: Fn(Result<Stmt, String>) -> bool,
    {
        match lexed {
            Some(result) => closure(result.data),
            None => false,
        }
    }
    fn match_type(lexed: Option<ParseType>, given_type: Type) -> bool {
        match_data(lexed, |data| match data {
            Ok(Stmt::Declaration(symbol)) => symbol.c_type == given_type,
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
        assert!(match_type(parse("void f();"), Type::Void));
        assert!(match_type(parse("const volatile int f;"), Type::Int(true)));
    }
    #[test]
    fn test_bad_decl_specs() {
        assert!(parse("int;").is_none());
        assert!(parse("char char;").unwrap().data.is_err());
        assert!(parse("char long;").unwrap().data.is_err());
        assert!(parse("long char;").unwrap().data.is_err());
        assert!(parse("float char;").unwrap().data.is_err());
        assert!(parse("float double;").unwrap().data.is_err());
        assert!(parse("double double;").unwrap().data.is_err());
        assert!(parse("double unsigned;").unwrap().data.is_err());
        assert!(parse("short double;").unwrap().data.is_err());
        assert!(parse("int void;").unwrap().data.is_err());
        assert!(parse("void int;").unwrap().data.is_err());
        // default to int if we don't have a type
        // don't panic if we see duplicate specifiers
        assert!(match_type(parse("unsigned unsigned i;"), Type::Int(false)));
        assert!(match_type(parse("extern extern i;"), Type::Int(true)));
        assert!(match_type(parse("const const i;"), Type::Int(true)));
        assert!(match_type(parse("const volatile i;"), Type::Int(true)));
    }
    #[test]
    fn test_complex_types() {
        // this is all super ugly
        use crate::data::{ArrayType, Qualifiers};
        use std::boxed::Box;
        use Type::*;
        assert!(match_type(
            parse("int a[]"),
            Array(Box::new(Int(true)), ArrayType::Unbounded)
        ));
        assert!(match_type(
            parse("unsigned a[]"),
            Array(Box::new(Int(false)), ArrayType::Unbounded)
        ));
        assert!(match_type(
            parse("float *a"),
            Pointer(Box::new(Float), Default::default())
        ));
        assert!(match_type(
            parse("float *const a"),
            Pointer(Box::new(Float), Qualifiers::CONST)
        ));
        assert!(match_type(
            parse("double *volatile *const a"),
            Pointer(
                Box::new(Pointer(Box::new(Double), Qualifiers::CONST)),
                Qualifiers::VOLATILE
            )
        ));
        assert!(match_type(
            parse("_Bool *volatile const a"),
            Pointer(Box::new(Bool), Qualifiers::CONST_VOLATILE)
        ));
        // cdecl: declare foo as array 10 of pointer to pointer to int
        assert!(match_type(
            parse("char **foo[10];"),
            Pointer(
                Box::new(Pointer(
                    Box::new(Array(
                        Box::new(Char(true)),
                        ArrayType::Fixed(Box::new(Expr::Int(Token::Int(10))))
                    )),
                    Default::default()
                )),
                Default::default()
            )
        ));
        // cdecl: declare foo as pointer to pointer to array 10 of int
        assert!(match_type(
            parse("int (**foo)[10];"),
            Array(
                Box::new(Pointer(
                    Box::new(Pointer(Box::new(Int(true)), Default::default())),
                    Default::default()
                )),
                ArrayType::Fixed(Box::new(Expr::Int(Token::Int(10))))
            )
        ));
    }

}
