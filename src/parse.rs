use std::{iter::Peekable, rc::Rc};

use crate::{
    ast::{Ast, BinOp, PrimFun, UnOp},
    token::{KeyWord, LexError, Token, TokenResult, TokenStream},
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ParseError {
    Lex(LexError),
    /// The parsing failed because there were leftover tokens at the end.
    SpareTokens,
    /// Reached EOF while parsing, and expected more tokens.
    ReachedEnd,
    /// Found an unexpected token while parsing.
    UnexpectedToken {
        got: Token,
        expected: String,
    },
}

impl From<LexError> for ParseError {
    fn from(e: LexError) -> Self {
        ParseError::Lex(e)
    }
}

/// An iterator which produces tokens.
pub type TokenPeeker<I> = Peekable<TokenStream<I>>;

pub type ParseResult = Result<Ast, ParseError>;

#[allow(unused)]
/// Parse a stream of tokens, and generate an AST from it. Consumes the token
/// stream.
pub fn parse<I: Iterator<Item = char>>(tokens: TokenStream<I>) -> ParseResult {
    let mut peeker = tokens.peekable();
    let result = parse_exp(&mut peeker)?;
    let n = peeker.next();
    if n != None {
        return Err(ParseError::SpareTokens);
    }

    Ok(result)
}

/// Parse an expression. Consumes all tokens associated with the expression.
fn parse_exp<I: Iterator<Item = char>>(tokens: &mut TokenPeeker<I>) -> ParseResult {
    let token = tokens.next().ok_or(ParseError::ReachedEnd)??;
    match token {
        Token::KeyWord(kw) => match kw {
            KeyWord::If => return parse_if(tokens),
            KeyWord::Let => return parse_let(tokens),
            KeyWord::Map => return parse_map(tokens),
            _ => (),
        },
        _ => (),
    };
    // a phrase beginning with a term, potentially followed by binary
    // operations.
    let mut exp = parse_term(tokens, token)?;
    loop {
        // find any binary operations
        let operator = match tokens.peek() {
            Some(Ok(Token::Plus)) => BinOp::Plus,
            Some(Ok(Token::Minus)) => BinOp::Minus,
            Some(Ok(Token::Slash)) => BinOp::Div,
            Some(Ok(Token::Star)) => BinOp::Mul,
            Some(Ok(Token::And)) => BinOp::And,
            Some(Ok(Token::Or)) => BinOp::Or,
            Some(Ok(Token::Eq)) => BinOp::Eq,
            Some(Ok(Token::Neq)) => BinOp::Neq,
            Some(Ok(Token::Gt)) => BinOp::Gt,
            Some(Ok(Token::Geq)) => BinOp::Geq,
            Some(Ok(Token::Lt)) => BinOp::Lt,
            Some(Ok(Token::Leq)) => BinOp::Leq,
            _ => break,
        };
        tokens.next(); // consume the peeked token
        let last_token = tokens.next().ok_or(ParseError::ReachedEnd)??;
        exp = Ast::BinOp {
            rator: operator,
            lhs: Rc::new(exp),
            rhs: Rc::new(parse_term(tokens, last_token)?),
        };
    }
    Ok(exp)
}

/// Parse an if statement. Assumes the `if` keyword has already been consumed.
fn parse_if<I: Iterator<Item = char>>(tokens: &mut TokenPeeker<I>) -> ParseResult {
    let condition = Rc::new(parse_exp(tokens)?);
    require_token(tokens.next(), Token::KeyWord(KeyWord::Then))?;
    let consequence = Rc::new(parse_exp(tokens)?);
    require_token(tokens.next(), Token::KeyWord(KeyWord::Else))?;
    let alternate = Rc::new(parse_exp(tokens)?);

    Ok(Ast::If {
        condition,
        consequence,
        alternate,
    })
}

/// Parse a let statement. Assumes that the `let` keyword has already been
/// consumed.
fn parse_let<I: Iterator<Item = char>>(tokens: &mut TokenPeeker<I>) -> ParseResult {
    let mut defs = Vec::new();
    let mut t = tokens.next();
    while t != Some(Ok(Token::KeyWord(KeyWord::In))) {
        let id = require_id(t.clone())?;
        require_token(tokens.next().clone(), Token::Walrus)?;
        let rhs = parse_exp(tokens)?;
        defs.push((id, rhs));
        require_token(tokens.next(), Token::Semicolon)?;
        t = tokens.next();
    }

    Ok(Ast::Let {
        defs,
        body: Rc::new(parse_exp(tokens)?),
    })
}

/// Parse a map statement. Assumes that the `map` keyword has already been
/// consumed.
fn parse_map<I: Iterator<Item = char>>(tokens: &mut TokenPeeker<I>) -> ParseResult {
    let mut params = Vec::new();
    let mut t = tokens.next();
    if t == Some(Ok(Token::KeyWord(KeyWord::To))) {
        return Ok(Ast::Map {
            params,
            body: Rc::new(parse_exp(tokens)?),
        });
    }
    loop {
        params.push(require_id(t)?);
        match tokens.next().ok_or(ParseError::ReachedEnd)?? {
            Token::Comma => t = tokens.next(),
            Token::KeyWord(KeyWord::To) => break,
            t => {
                return Err(ParseError::UnexpectedToken {
                    got: t,
                    expected: "identifier".into(),
                })
            }
        };
    }

    Ok(Ast::Map {
        params,
        body: Rc::new(parse_exp(tokens)?),
    })
}

/// Parse a term, which may be some number of unary operators followed by a
/// constant or variable.
fn parse_term<I: Iterator<Item = char>>(
    tokens: &mut TokenPeeker<I>,
    last_token: Token,
) -> ParseResult {
    match last_token {
        Token::Tilde => {
            let next_tok = tokens.next().ok_or(ParseError::ReachedEnd)??;
            Ok(Ast::UnOp {
                rator: UnOp::Not,
                operand: Rc::new(parse_term(tokens, next_tok)?),
            })
        }
        Token::Minus => {
            let next_tok = tokens.next().ok_or(ParseError::ReachedEnd)??;
            Ok(Ast::UnOp {
                rator: UnOp::Neg,
                operand: Rc::new(parse_term(tokens, next_tok)?),
            })
        }
        Token::KeyWord(kw) => match kw {
            KeyWord::Empty => Ok(Ast::Empty),
            KeyWord::True => Ok(Ast::Bool(true)),
            KeyWord::False => Ok(Ast::Bool(false)),
            _ => Err(ParseError::UnexpectedToken {
                got: last_token,
                expected: "constant".into(),
            }),
        },
        Token::Number(num) => Ok(Ast::Int(num)),
        _ => {
            let factor = parse_factor(tokens, last_token)?;

            Ok(match tokens.peek() {
                Some(Ok(Token::LeftParenthesis)) => {
                    // function was actually applied, go grab the arguments
                    tokens.next();
                    let params = parse_args(tokens)?;
                    Ast::App {
                        rator: Rc::new(factor),
                        params,
                    }
                }
                _ => factor,
            })
        }
    }
}

/// Parse the head of a function application. Takes in the last token that was
/// used to make its requisite term, plus the remaining terms.
fn parse_factor<I: Iterator<Item = char>>(
    tokens: &mut TokenPeeker<I>,
    last_token: Token,
) -> ParseResult {
    match last_token {
        Token::LeftParenthesis => {
            let exp = parse_exp(tokens)?;
            require_token(tokens.next(), Token::RightParenthesis)?;
            Ok(exp)
        }
        Token::Id(s) => Ok(match s.as_str() {
            "number?" => Ast::Primitive(PrimFun::IsNumber),
            "function?" => Ast::Primitive(PrimFun::IsFunction),
            "list?" => Ast::Primitive(PrimFun::IsList),
            "empty?" => Ast::Primitive(PrimFun::IsEmpty),
            "cons?" => Ast::Primitive(PrimFun::IsCons),
            "cons" => Ast::Primitive(PrimFun::Cons),
            "first" => Ast::Primitive(PrimFun::First),
            "rest" => Ast::Primitive(PrimFun::Rest),
            "arity" => Ast::Primitive(PrimFun::Arity),
            _ => Ast::Variable(s),
        }),
        t => Err(ParseError::UnexpectedToken {
            got: t,
            expected: "`)` or identifer".into(),
        }),
    }
}

/// Parse a comma separated list, as well as consuming the token immediately
/// following the list. Consumes the closing right parenthesis as well.
fn parse_args<I: Iterator<Item = char>>(
    tokens: &mut TokenPeeker<I>,
) -> Result<Vec<Ast>, ParseError> {
    let mut args = Vec::new();
    if tokens.peek() == Some(&Ok(Token::RightParenthesis)) {
        tokens.next();
        return Ok(args);
    }
    loop {
        args.push(parse_exp(tokens)?);
        match tokens.next().ok_or(ParseError::ReachedEnd)?? {
            Token::RightParenthesis => return Ok(args),
            Token::Comma => (),
            t => {
                return Err(ParseError::UnexpectedToken {
                    got: t,
                    expected: "`)` or `,`".into(),
                })
            }
        }
    }
}

/// Require that `token` be an identifier, and return the string it identifies, 
/// or a `ParseError` if not.
fn require_id(token: Option<TokenResult>) -> Result<String, ParseError> {
    match token.ok_or(ParseError::ReachedEnd)?? {
        Token::Id(s) => Ok(s),
        t => Err(ParseError::UnexpectedToken {
            got: t,
            expected: "identifier".into(),
        }),
    }
}

/// Require that the token be equal to the expected token. Returns an `Err` if 
/// this is not the case.
fn require_token(token: Option<TokenResult>, required: Token) -> Result<(), ParseError> {
    let t = token.ok_or(ParseError::ReachedEnd)??;
    if required == t {
        Ok(())
    } else {
        Err(ParseError::UnexpectedToken {
            got: t,
            expected: format!("{required}"),
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::token::TokenStream;

    use super::*;

    #[test]
    fn test_parse_constant() {
        parse_helper("12345", Ok(Ast::Int(12345)));
    }

    #[test]
    fn test_parse_unary_negation() {
        parse_helper(
            "-123",
            Ok(Ast::UnOp {
                rator: UnOp::Neg,
                operand: Rc::new(Ast::Int(123)),
            }),
        );
    }

    #[test]
    fn test_parse_application() {
        parse_helper(
            "f(x) + (x*12)",
            Ok(Ast::BinOp {
                rator: BinOp::Plus,
                lhs: Rc::new(Ast::App {
                    rator: Rc::new(Ast::Variable("f".into())),
                    params: vec![Ast::Variable("x".into())],
                }),
                rhs: Rc::new(Ast::BinOp {
                    rator: BinOp::Mul,
                    lhs: Rc::new(Ast::Variable("x".into())),
                    rhs: Rc::new(Ast::Int(12)),
                }),
            }),
        );
    }

    #[test]
    fn test_parse_lists() {
        parse_helper(
            "first(cons(1, empty))",
            Ok(Ast::App {
                rator: Rc::new(Ast::Primitive(PrimFun::First)),
                params: vec![Ast::App {
                    rator: Rc::new(Ast::Primitive(PrimFun::Cons)),
                    params: vec![Ast::Int(1), Ast::Empty],
                }],
            }),
        );
    }

    #[test]
    fn test_parse_let() {
        parse_helper(
            "let a := 3; in a + a",
            Ok(Ast::Let { 
                defs: vec![("a".into(), Ast::Int(3))], 
                body: Rc::new(Ast::BinOp { 
                    rator: BinOp::Plus, 
                    lhs: Rc::new(Ast::Variable("a".into())), 
                    rhs: Rc::new(Ast::Variable("a".into())) 
                })
            })
        )
    }

    fn parse_helper(input: &str, expected: ParseResult) {
        let ast = parse(TokenStream::new(input.chars()));
        assert_eq!(ast, expected);
    }
}
