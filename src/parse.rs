use std::collections::{HashSet, VecDeque};
use std::convert::TryFrom;
use std::iter::{Iterator, Peekable};

use crate::data::{
    Expr, Keyword, Locatable, Location, Qualifiers, Stmt, StorageClass, Symbol, Token, Type,
};
use crate::utils::{error, warn};

type Lexeme<'a> = Locatable<'a, Result<Token, String>>;

#[derive(Debug)]
pub struct Parser<'a, I: Iterator<Item = Lexeme<'a>>> {
    tokens: Peekable<I>,
    pending: VecDeque<Locatable<'a, Result<Stmt, String>>>,
    current: Option<Lexeme<'a>>,
}

impl<'a, I> Parser<'a, I>
where
    I: Iterator<Item = Lexeme<'a>>,
{
    pub fn new(iter: I) -> Self {
        Parser {
            tokens: iter.peekable(),
            pending: Default::default(),
            current: None,
        }
    }
}

impl<'a, I: Iterator<Item = Lexeme<'a>>> Iterator for Parser<'a, I> {
    type Item = Locatable<'a, Result<Stmt, String>>;
    fn next(&mut self) -> Option<Self::Item> {
        self.pending.pop_front().or_else(|| {
            let Locatable { data, location } = self.next_token()?;
            match data {
                Ok(lexed) => match lexed {
                    // NOTE: we do not allow implicit int
                    // https://stackoverflow.com/questions/11064292
                    Token::Keyword(t) if t.is_decl_specifier() => self.parse_decl(t),
                    _ => Some(Locatable {
                        data: Err("not handled".to_string()),
                        location,
                    }),
                },
                Err(err) => {
                    error(&err, &location);
                    // NOTE: returning from closure, not from `next()`
                    self.next()
                }
            }
        })
    }
}
#[inline]
/* the reason this is such a mess (instead of just putting everything into
 * the hashmap, which would be much simpler logic) is so we have a Location
 * to go with every error */
fn handle_single_decl_specifier<'a>(
    keyword: Keyword,
    storage_class: &mut Option<StorageClass>,
    qualifiers: &mut Qualifiers,
    keywords: &mut HashSet<Keyword>,
    ctype: &mut Option<Type>,
    signed: &mut Option<bool>,
    errors: &mut Vec<Locatable<'a, String>>,
    location: Location<'a>,
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
    // we don't want to reset it if true
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

impl<'a, I: Iterator<Item = Lexeme<'a>>> Parser<'a, I> {
    fn next_token(&mut self) -> Option<Lexeme<'a>> {
        self.current = self.tokens.next();
        self.current.clone()
    }
    fn expect(&mut self, next: Token) -> (bool, Location<'a>) {
        match self.tokens.peek() {
            Some(Locatable {
                data: Ok(token), ..
            }) if *token == next => (true, self.next_token().unwrap().location),
            Some(Locatable { location, data }) => {
                let location = location.clone();
                self.pending.push_back(Locatable {
                    location: location.clone(),
                    data: Err(format!(
                        "expected '{}', got '{}'",
                        next,
                        data.clone()
                            .unwrap_or_else(|_| Token::Id("<lex error>".to_string()))
                    )),
                });
                (false, location)
            }
            None => {
                let location = self
                    .current
                    .clone()
                    .expect("expect cannot be called at start of program")
                    .location;
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
    ) -> Result<(StorageClass, Qualifiers, Type), Locatable<'a, String>> {
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
        while let Some(locatable) = self.tokens.peek() {
            let keyword = match locatable.data {
                Ok(Token::Keyword(k)) if k.is_decl_specifier() => k,
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
                // if there's no next token, they left out part of the
                // program and we'll throw an error in just a second
                // besides, it makes getting a location really hard
                if let Some(locatable) = self.tokens.peek() {
                    if signed.is_none() {
                        warn(
                            &"type specifier missing, defaults to int".to_string(),
                            &locatable.location,
                        );
                    }
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
    fn parse_type(
        &mut self,
        ctype: &Type,
    ) -> Option<Locatable<'a, Result<(String, Type), String>>> {
        if let Some(Locatable {
            data: Ok(next),
            location,
        }) = self.tokens.peek()
        {
            match next {
                Token::LeftParen => {
                    self.next_token();
                    let next = self.parse_type(ctype);
                    self.expect(Token::RightParen);
                    next
                }
                Token::Star => {
                    self.next_token();
                    match self.parse_type(ctype) {
                        Some(Locatable {
                            location,
                            data: Ok((id, ctype)),
                        }) => Some(Locatable {
                            location,
                            data: Ok((id, Type::Pointer(Box::new(ctype)))),
                        }),
                        x => x,
                    }
                }
                _ => None,
            }
        } else {
            None
        }
    }
    // NOTE: there's some fishiness here. Declarations can have multiple variables,
    // but we typed them as only having one Symbol. Wat do?
    // We push all but one declaration into the 'pending' vector
    // and return the last.
    fn parse_decl(&mut self, start: Keyword) -> Option<Locatable<'a, Result<Stmt, String>>> {
        let (sc, qualifiers, ctype) = match self.parse_decl_specifiers(start) {
            Ok(tuple) => tuple,
            Err(err) => {
                return Some(Locatable {
                    data: Err(err.data),
                    location: err.location,
                });
            }
        };
        let mut has_valid = false;
        while let Some(Locatable {
            data: ctype,
            location,
        }) = self.parse_type(&ctype)
        {
            println!("got decl: {:?}", ctype);
            match ctype {
                Ok(decl) => {
                    has_valid = true;
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
        }
        let (matched, location) = self.expect(Token::Semicolon);
        if matched && !has_valid {
            warn(
                &"declaration does not declare anything".to_string(),
                &location,
            );
        }
        // this is empty when we had specifiers without identifiers
        // e.g. `int;`
        self.pending.pop_front().or_else(|| self.next())
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
    use crate::data::{Locatable, Stmt, Type};
    use crate::Lexer;
    type ParseType<'a> = Locatable<'a, Result<Stmt, String>>;
    fn parse<'a>(input: &'a str) -> Option<ParseType<'a>> {
        parse_all(input).get(0).map(|x| x.clone())
    }
    fn parse_all<'a>(input: &'a str) -> Vec<ParseType<'a>> {
        Parser::new(Lexer::new("<test suite>", input.chars())).collect()
    }
    fn match_data<'a, T>(lexed: Option<ParseType<'a>>, closure: T) -> bool
    where
        T: Fn(Result<Stmt, String>) -> bool,
    {
        match lexed {
            Some(result) => closure(result.data),
            None => false,
        }
    }
    fn match_type<'a>(lexed: Option<ParseType<'a>>, given_type: Type) -> bool {
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
        assert!(parse("char char").unwrap().data.is_err());
        assert!(parse("char long").unwrap().data.is_err());
        assert!(parse("long char").unwrap().data.is_err());
        assert!(parse("float char").unwrap().data.is_err());
        assert!(parse("float double").unwrap().data.is_err());
        assert!(parse("double double").unwrap().data.is_err());
        assert!(parse("double unsigned").unwrap().data.is_err());
        assert!(parse("short double").unwrap().data.is_err());
        assert!(parse("int void").unwrap().data.is_err());
        assert!(parse("void int").unwrap().data.is_err());
        // default to int if we don't have a type
        // don't panic if we see duplicate specifiers
        assert!(match_type(parse("unsigned unsigned"), Type::Int(false)));
        assert!(match_type(parse("extern extern"), Type::Int(true)));
        assert!(match_type(parse("const const"), Type::Int(true)));
        assert!(match_type(parse("const volatile"), Type::Int(true)));
    }
}
