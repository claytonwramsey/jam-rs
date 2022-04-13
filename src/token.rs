//! A module containing tools for tokenizing a Jam program into a
//! parser-friendly LL(1) format.

use std::{fmt::Display, iter::Peekable};

#[derive(Clone, PartialEq, Eq, Debug)]
/// The types of tokens which are emitted by the tokenization process.
pub enum Token {
    /// Any string identifier. Starts any alphabetic character, an underscore,
    /// or a question mark, and is followed by any number of those or digits.
    Id(String),
    /// A numeric literal. Will always be positive (as negatives are expressed
    /// as operators)
    Number(u32),
    /// A reserved keyword.
    KeyWord(KeyWord),
    /// `(`.
    LeftParenthesis,
    /// `)`.
    RightParenthesis,
    /// `,`.
    Comma,
    /// `;`.
    Semicolon,
    /// `+`.
    Plus,
    /// `-`.
    Minus,
    /// `~`.
    Tilde,
    /// `*`.
    Star,
    /// `/`.
    Slash,
    /// `=`.
    Eq,
    /// `!=`.
    Neq,
    /// `<`.
    Lt,
    /// `>`.
    Gt,
    /// `<=`.
    Leq,
    /// `>=`.
    Geq,
    /// `&`.
    And,
    /// `|`.
    Or,
    /// The walrus `:=` operator, used in lets.
    Walrus,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// The set of reserved keywords.
pub enum KeyWord {
    If,
    Then,
    Else,
    Map,
    To,
    Let,
    In,
    Empty,
    True,
    False,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// The types of errors which can occur during the lexing process.
pub enum LexError {
    /// Unrecognized character.
    Unrecognized(char),
    /// Expected a certain character, but got a different one, or reached EOF.
    Unexpected { expected: char, got: Option<char> },
}

/// The result of asking for another token from the lexer.
pub type TokenResult = Result<Token, LexError>;

/// A stream of tokens.
pub struct TokenStream<I: Iterator<Item = char>> {
    /// The source of the tokens.
    source: Peekable<I>,
}

impl<I: Iterator<Item = char>> TokenStream<I> {
    #[allow(unused)]
    /// Construct a new `TokenStream` for any source which can iterate over
    /// characters.
    pub fn new(iter: I) -> TokenStream<I> {
        TokenStream {
            source: iter.peekable(),
        }
    }
}

impl<I: Iterator<Item = char>> Iterator for TokenStream<I> {
    type Item = TokenResult;

    /// Get the next token. Will return a `LexError` if it is unable to parse
    /// out a token, either due to the source of characters running out or
    /// providing an unexpected character.
    fn next(&mut self) -> Option<Self::Item> {
        Some(Ok(match self.source.next()? {
            '(' => Token::LeftParenthesis,
            ')' => Token::RightParenthesis,
            ',' => Token::Comma,
            ';' => Token::Semicolon,
            '+' => Token::Plus,
            '-' => Token::Minus,
            '~' => Token::Tilde,
            '*' => Token::Star,
            '/' => Token::Slash,
            '&' => Token::And,
            '|' => Token::Or,
            '=' => Token::Eq,
            '!' => {
                let c = self.source.next();
                if c != Some('=') {
                    return Some(Err(LexError::Unexpected {
                        expected: '=',
                        got: c,
                    }));
                }
                Token::Neq
            }
            '<' => match self.source.peek() {
                Some('=') => {
                    self.source.next();
                    Token::Leq
                }
                _ => Token::Lt,
            },

            '>' => match self.source.peek() {
                Some('=') => {
                    self.source.next();
                    Token::Geq
                }
                _ => Token::Gt,
            },
            ':' => {
                let c = self.source.next();
                if c != Some('=') {
                    return Some(Err(LexError::Unexpected {
                        expected: '=',
                        got: c,
                    }));
                }
                Token::Walrus
            }
            c if c.is_whitespace() => return self.next(),
            c if c.is_alphabetic() || c == '_' || c == '?' => {
                // identifier
                let mut s: String = c.into();
                while let Some(&c) = self.source.peek() {
                    if !(c.is_alphanumeric() || c == '_' || c == '?') {
                        break;
                    }
                    s.push(self.source.next().unwrap());
                }
                match s.as_str() {
                    "if" => Token::KeyWord(KeyWord::If),
                    "then" => Token::KeyWord(KeyWord::Then),
                    "else" => Token::KeyWord(KeyWord::Else),
                    "map" => Token::KeyWord(KeyWord::Map),
                    "to" => Token::KeyWord(KeyWord::To),
                    "let" => Token::KeyWord(KeyWord::Let),
                    "in" => Token::KeyWord(KeyWord::In),
                    "empty" => Token::KeyWord(KeyWord::Empty),
                    "true" => Token::KeyWord(KeyWord::True),
                    "false" => Token::KeyWord(KeyWord::False),
                    _ => Token::Id(s),
                }
            }
            c if c.is_numeric() => {
                // number literal
                let mut s: String = c.into();
                while let Some(&c) = self.source.peek() {
                    if !(c.is_numeric()) {
                        break;
                    }
                    s.push(self.source.next().unwrap())
                }
                Token::Number(s.parse().unwrap())
            }
            '\0' => return None,
            c => return Some(Err(LexError::Unrecognized(c))),
        }))
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Id(s) => write!(f, "{s}"),
            Token::Number(n) => write!(f, "{n}"),
            Token::KeyWord(kw) => write!(f, "{kw}"),
            Token::LeftParenthesis => write!(f, "("),
            Token::RightParenthesis => write!(f, ")"),
            Token::Comma => write!(f, ","),
            Token::Semicolon => write!(f, ";"),
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Tilde => write!(f, "~"),
            Token::Star => write!(f, "*"),
            Token::Slash => write!(f, "/"),
            Token::Eq => write!(f, "="),
            Token::Neq => write!(f, "!="),
            Token::Lt => write!(f, "<"),
            Token::Gt => write!(f, ">"),
            Token::Leq => write!(f, "<="),
            Token::Geq => write!(f, ">="),
            Token::And => write!(f, "&"),
            Token::Or => write!(f, "|"),
            Token::Walrus => write!(f, ":="),
        }
    }
}

impl Display for KeyWord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                KeyWord::If => "if",
                KeyWord::Then => "then",
                KeyWord::Else => "else",
                KeyWord::Map => "map",
                KeyWord::To => "to",
                KeyWord::Let => "let",
                KeyWord::In => "in",
                KeyWord::Empty => "empty",
                KeyWord::True => "true",
                KeyWord::False => "false",
            }
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kw_let() {
        tokenize_helper("let", &[Some(Ok(Token::KeyWord(KeyWord::Let))), None]);
    }

    #[test]
    fn test_id() {
        tokenize_helper("bog2", &[Some(Ok(Token::Id("bog2".into()))), None]);
    }

    #[test]
    fn test_number() {
        tokenize_helper("123", &[Some(Ok(Token::Number(123))), None]);
    }

    /// Helper function for tokenizer testing. Requires that the token stream
    /// provides the results of `expected` in order.
    fn tokenize_helper(source: &str, expected: &[Option<TokenResult>]) {
        let mut stream = TokenStream::new(source.chars());
        for expect in expected {
            assert_eq!(*expect, stream.next());
        }
    }
}
