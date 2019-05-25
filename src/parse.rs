use std::collections::{HashSet, VecDeque};
use std::convert::TryFrom;
use std::iter::{Iterator, Peekable};

use crate::utils::{error, warn};
use crate::data::{Symbol, Expr, Keyword,
                  Location, Locatable, Qualifiers, StorageClass, Stmt, Token, Type};

type Lexeme<'a> = Locatable<'a, Result<Token, String>>;

#[derive(Debug)]
pub struct Parser<'a, I: Iterator<Item = Lexeme<'a>>> {
    tokens: Peekable<I>,
    pending: VecDeque<Locatable<'a, Result<Stmt, String>>>
}

impl<'a, I> Parser<'a, I> where I: Iterator<Item = Lexeme<'a>> {
    pub fn new(iter: I) -> Self {
        Parser { tokens: iter.peekable(), pending: Default::default() }
    }
}

impl<'a, I: Iterator<Item = Lexeme<'a>>> Iterator for Parser<'a, I> {
    type Item = Locatable<'a, Result<Stmt, String>>;
    fn next(&mut self) -> Option<Self::Item> {
        self.pending.pop_front().or_else(|| {
            let token = self.tokens.next()?;
            Some(match token.data {
                Ok(lexed) => match lexed {
                    Token::Keyword(t) if t.is_decl_specifier() => self.parse_decl(t),
                    _ => Locatable {
                        data: Err("not handled".to_string()),
                        location: token.location
                    }
                },
                Err(err) => {
                    error(&err, &token.location);
                    // NOTE: returning from closure, not from `next()`
                    return self.next()
                }
            })
        })
    }
}
#[inline]
/* the reason this is such a mess (instead of just putting everything into
 * the hashmap, which would be much simpler logic) is so we have a Location
 * to go with every error */
fn handle_single_decl_specifier<'a>(keyword: Keyword,
                                storage_class: &mut Option<StorageClass>,
                                qualifiers: &mut Qualifiers,
                                keywords: &mut HashSet<Keyword>,
                                ctype: &mut Option<Type>,
                                signed: &mut Option<bool>,
                                errors: &mut Vec<Locatable<'a, String>>,
                                location: Location<'a>) {
    if !keywords.insert(keyword) {  // duplicate
        // we can guess that they just meant to write it once
        if keyword.is_qualifier() || keyword.is_storage_class()
            || keyword == Keyword::Signed || keyword == Keyword::Unsigned {
            warn(&format!("duplicate declaration specifier '{}'", keyword),
                &location);
        // what is `short short` supposed to be?
        } else if keyword != Keyword::Long {
            errors.push(Locatable {
                data: format!("duplicate basic type '{}' in declarator", keyword),
                location: location.clone()
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
                location: location.clone()
            });
        }
        if *signed == None {
            *signed = Some(keyword == Keyword::Signed);
        } else if signed.unwrap() != (keyword == Keyword::Signed) {
            errors.push(Locatable {
                data: "values cannot be both signed and unsigned".to_string(),
                location: location
            });
        }
    } else if let Ok(sc) = StorageClass::try_from(keyword) {
        if *storage_class == None {
            *storage_class = Some(sc);
        } else {
            errors.push(Locatable {
                data: format!("multiple storage classes in declaration \
                              ('{}' and '{}')", storage_class.unwrap(), sc),
                location: location
            });
        }
    } else if keyword == Keyword::Float || keyword == Keyword::Double {
        if *signed != None {

        } else if keyword == Keyword::Float {
            if *ctype == Some(Type::Double) {
                errors.push(Locatable {
                      data: "two or more data types in declaration specifiers".to_string(),
                      location: location
                });
            }
            *ctype = Some(Type::Float);
        } else {
            *ctype = Some(Type::Double);
        }
    } else {
        println!("we think {} is an int type, are we right?", keyword);
    }
}
impl<'a, I: Iterator<Item = Lexeme<'a>>> Parser<'a, I> {
    // this is an utter hack
    // NOTE: the reason the return type is so weird (Result<_, Locatable<_>)
    // is because declaration specifiers can never be a statement on their own:
    // the associated location always belongs to the identifier
    fn parse_decl_specifiers(&mut self, start: Keyword) ->
            Result<(StorageClass, Qualifiers, Type), Locatable<'a, String>> {
        let mut keywords = HashSet::new();
        keywords.insert(start);
        let mut storage_class = StorageClass::try_from(start).ok();
        let mut qualifiers = Qualifiers {
            c_const: start == Keyword::Const,
            volatile: start == Keyword::Volatile
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
                _ => break
            };
            let locatable = self.tokens.next().unwrap();
            handle_single_decl_specifier(keyword, &mut storage_class,
                                         &mut qualifiers, &mut keywords,
                                         &mut ctype, &mut signed, &mut errors,
                                         locatable.location);
        }
        while errors.len() > 1 {
            let current = errors.pop().unwrap();
            error(&current.data, &current.location);
        }
        if errors.len() != 0 {
            Err(errors.pop().unwrap())
        } else {
            // TODO: set signed
            let ctype = ctype.unwrap_or_else(|| {
                // if there's no next token, they left out part of the
                // program and we'll throw an error in just a second
                // besides, it makes getting a location really hard
                if let Some(locatable) = self.tokens.peek() {
                    warn(&"type specifier missing, defaults to int".to_string(),
                         &locatable.location);
                }
                Type::Int(true)
            });
            Ok((storage_class.unwrap_or(StorageClass::Auto), qualifiers, ctype))
        }
    }
    // NOTE: there's some fishiness here. Declarations can have multiple variables,
    // but we typed them as only having one Symbol. Wat do?
    // We push all but one declaration into the 'pending' vector
    // and return the last.
    fn parse_decl(&mut self, start: Keyword) -> Locatable<'a, Result<Stmt, String>> {
        let (sc, qualifiers, ctype) = match self.parse_decl_specifiers(start) {
            Ok(tuple) => tuple,
            Err(err) => return Locatable {
                data: Err(err.data),
                location: err.location
            }
        };
        Locatable {
            data: Ok(Stmt::Declaration(Symbol {
                id: "a".to_string(),
                c_type: ctype,
                qualifiers: qualifiers,
                storage_class: sc
            })),
            location: Location {
                file: "literally made this up",
                line: 0,
                column: 0
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
    fn is_decl_specifier(self) -> bool {
        use Keyword::*;
        match self {
            Unsigned|Signed|Char|Short|Int|Long|Float|Double|
            Extern|Static|Auto|Register|Const|Volatile => true,
            _ => false
        }
    }
    fn is_base_type(self) -> bool {
        Type::try_from(self).is_ok()
    }
}

impl TryFrom<Keyword> for Type {
    type Error = ();
    fn try_from(keyword: Keyword) -> Result<Type, ()> {
        use Type::*;
        match keyword {
            Keyword::Void => Ok(Void),
            Keyword::Char => Ok(Char(true)),
            Keyword::Short => Ok(Short(true)),
            Keyword::Int => Ok(Int(true)),
            Keyword::Long => Ok(Long(true)),
            Keyword::Float => Ok(Float),
            Keyword::Double => Ok(Double),
            _ => Err(())
        }
    }
}
