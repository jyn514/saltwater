use super::data::{Location, Locatable, Token, TokenType, Error};

pub type Lexer<'a> = Locatable<'a, &'a Iterator<Item = char>>;

impl<'a> Lexer<'a> {
    pub fn new(filename: &'a str, stream: &'a Iterator<Item = char>) -> Lexer<'a> {
        Lexer {
            location: Location {
                line: 1,
                column: 1,
                file: filename
            },
            data: stream
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    // option: whether the stream is exhausted
    // result: whether the next lexeme is an error
    type Item = Result<Token<'a>, Error<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        let token = match self.data.next() {
            Some(c) => {
                TokenType::Plus
            },
            None => return None
        };
        Some(Ok(Token {
            location: self.location.clone(),
            data: token
        }))
    }
}
