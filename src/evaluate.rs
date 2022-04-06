use std::rc::Rc;

use crate::{value::{Value, ListVal}, binding::Environment, ast::{Ast, PrimFun, BinOp, UnOp}};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalError<E: Environment> {
    /// A variable was unbound and occurred free.
    Unbound(String),
    /// The program attempted to call something which was not a function.
    NotAFunction(Value<E>),
    /// The program called a function with the wrong number of arguments.
    WrongArgCount{
        expected: usize, 
        actual: usize,
    },
    /// The wrong type was given as a parameter to a primitive function.
    WrongPrimArg(PrimFun, Value<E>),
    /// The wrong type was given to a binary operator.
    WrongBinOpArg(BinOp, Value<E>),
    /// The wrong value was given to a unary operator.
    WrongUnOpArg(UnOp, Value<E>),
    /// The condition to an if statement was not a bool.
    TestNonBool(Value<E>),
    /// Divide by zero was attempted.
    DivZero
}

/// The result of an evaluation process.
pub type EvalResult<E> = Result<Value<E>, EvalError<E>>;

#[allow(unused)]
pub fn evaluate<E: Environment>(ast: &Ast) -> EvalResult<E> {
    evaluate_help(ast, &mut E::default())
}

pub fn evaluate_help<E: Environment>(
    ast: &Ast, 
    environment: &mut E
) -> EvalResult<E> {
    Ok(match ast {
        Ast::Int(n) => Value::Int(*n as i32),
        Ast::Bool(b) => Value::Bool(*b),
        Ast::Empty => Value::List(ListVal::Empty),
        Ast::Variable(v) => environment.get(v)?,
        Ast::Primitive(f) => Value::Primitive(*f),
        Ast::App { rator, params } => {
            let resolved_rator = evaluate_help(rator, environment)?;
            match resolved_rator {
                Value::Closure { 
                    params: keys, 
                    environment: closure_environment, 
                    body 
                } => {
                    if keys.len() != params.len() {
                        return Err(EvalError::WrongArgCount { 
                            expected: keys.len(), 
                            actual: params.len() 
                        });
                    }

                    let mut new_env = closure_environment.clone();
                    for (key, param) in keys.iter().zip(params.iter()) {
                        new_env.store(environment, key, param)?;
                    };

                    evaluate_help(&body, &mut new_env)?
                },
                Value::Primitive(f) => {
                    let mut args = Vec::new();
                    for param in params {
                        args.push(evaluate_help(param, environment)?);
                    }
                    eval_primitive(f, args)?
                },
                _ => return Err(EvalError::NotAFunction(resolved_rator))
            }
        },
        Ast::BinOp { rator, lhs, rhs } => {
            let lval = evaluate_help(&lhs, environment)?;
            let rval = evaluate_help(&rhs, environment)?;
            eval_binop(*rator, lval, rval)?
        },
        Ast::UnOp { rator, operand } => {
            let arg = evaluate_help(&operand, environment)?;
            match rator {
                UnOp::Not => {
                    match arg {
                        Value::Bool(b) => Value::Bool(!b),
                        _ => return Err(EvalError::WrongUnOpArg(*rator, arg)),
                    }
                },
                UnOp::Neg => {
                    match arg {
                        Value::Int(x) => Value::Int(-x),
                        _ => return Err(EvalError::WrongUnOpArg(*rator, arg))
                    }
                },
            }
        },
        Ast::If { condition, consequence, alternate } => {
            let test_val = evaluate_help(condition, environment)?;
            match test_val {
                Value::Bool(true) => evaluate_help(consequence, environment)?,
                Value::Bool(false) => evaluate_help(alternate, environment)?,
                _ => return Err(EvalError::TestNonBool(test_val)),
            }
        },
        Ast::Let { defs, body } => {
            let mut new_env = environment.clone();
            for (key, def_body) in defs.iter() {
                new_env.store(environment, key, def_body)?;
            }
            evaluate_help(body, environment)?
        },
        Ast::Map { params, body } => Value::Closure { 
            params: params.clone(), 
            environment: environment.clone(), 
            body: body.clone(),
        },
    })
}

fn eval_primitive<E: Environment>(
    f: PrimFun, 
    args: Vec<Value<E>>, 
) -> EvalResult<E> {
    let require_param_len = |n| match args.len() == n {
        true => Ok(()),
        false => Err(EvalError::WrongArgCount { 
            expected: n, 
            actual: args.len() 
        })
    };
    Ok(match f {
        PrimFun::IsNumber => {
            require_param_len(1)?;
            Value::Bool(matches!(args[0], Value::Bool(_)))
        },
        PrimFun::IsFunction => {
            require_param_len(1)?;
            Value::Bool(matches!(
                args[0], 
                Value::Closure{params: _, environment: _, body: _} 
                | Value::Primitive(_)
            ))
        },
        PrimFun::IsList => {
            require_param_len(1)?;
            Value::Bool(matches!(args[0], Value::List(_)))
        },
        PrimFun::IsEmpty => {
            require_param_len(1)?;
            Value::Bool(matches!(args[0], Value::List(ListVal::Empty)))
        },
        PrimFun::IsCons => {
            require_param_len(1)?;
            Value::Bool(matches!(args[0], Value::List(ListVal::Cons {
                head: _, 
                tail: _,
            })))
        },
        PrimFun::Cons => {
            require_param_len(2)?;
            match args[1].to_owned() {
                Value::List(l) => Value::List(ListVal::Cons { 
                    head: Rc::new(args[0].to_owned()), 
                    tail: Rc::new(l), 
                }),
                a => return Err(EvalError::WrongPrimArg(f, a))
            }
        },
        PrimFun::First => {
            require_param_len(1)?;
            match args[0].to_owned() {
                Value::List(ListVal::Cons{head, tail: _}) => head.as_ref().clone(),
                a => return Err(EvalError::WrongPrimArg(f, a)),
            }
        },
        PrimFun::Rest => {
            require_param_len(1)?;
            match args[0].to_owned() {
                Value::List(ListVal::Cons{head: _, tail}) => Value::List(
                    tail.as_ref().clone()
                ),
                a => return Err(EvalError::WrongPrimArg(f, a)),
            }
        },
        PrimFun::Arity => {
            require_param_len(1)?;
            match args[0].to_owned() {
                Value::Primitive(p) => Value::Int(match p {
                    PrimFun::Cons => 2,
                    _ => 1,
                }),
                Value::Closure { params, environment: _, body: _} => {
                    Value::Int(params.len() as i32)
                },
                a => return Err(EvalError::WrongPrimArg(f, a)),
            }
        },
    })
}

/// Evaluate a binary operation `op`. Returns an error in case of a type error 
/// or a divide by zero.
fn eval_binop<E: Environment>(
    op: BinOp, 
    lhs: Value<E>, 
    rhs: Value<E>
) -> EvalResult<E> {
    Ok(match op {
        BinOp::Plus => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Int(a + b)
        },
        BinOp::Minus => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Int(a - b)
        },
        BinOp::Div => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            if b == 0 {
                return Err(EvalError::DivZero);
            }
            Value::Int(a / b)
        },
        BinOp::Mul => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Int(a * b)
        },
        BinOp::And => {
            let (a, b) = require_binop_bool(lhs, rhs, op)?;
            Value::Bool(a && b)
        },
        BinOp::Or => {
            let (a, b) = require_binop_bool(lhs, rhs, op)?;
            Value::Bool(a || b)
        },
        BinOp::Eq => Value::Bool(lhs == rhs),
        BinOp::Neq => Value::Bool(lhs != rhs),
        BinOp::Gt => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Bool(a > b)
        },
        BinOp::Geq => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Bool(a >= b)
        },
        BinOp::Lt => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Bool(a < b)
        },
        BinOp::Leq => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Bool(a <= b)
        },
    })
}

/// Require that `lhs` and `rhs` be integers, or return an error if they are 
/// not. Return the contained integers on `Ok()`.
fn require_binop_int<E: Environment>(
    lhs: Value<E>, 
    rhs: Value<E>, 
    op: BinOp
) -> Result<(i32, i32), EvalError<E>> {
    match (lhs, rhs) {
        (Value::Int(a), Value::Int(b)) => Ok((a, b)),
        (val, Value::Int(_)) => Err(EvalError::WrongBinOpArg(op, val)),
        (_, val) => Err(EvalError::WrongBinOpArg(op, val))
    }
}

/// Require that `lhs` and `rhs` be booleans, or return an error if they are 
/// not. Return the contained booleans on `Ok()`.
fn require_binop_bool<E: Environment>(
    lhs: Value<E>, 
    rhs: Value<E>, 
    op: BinOp
) -> Result<(bool, bool), EvalError<E>> {
    match (lhs, rhs) {
        (Value::Bool(a), Value::Bool(b)) => Ok((a, b)),
        (val, Value::Bool(_)) => Err(EvalError::WrongBinOpArg(op, val)),
        (_, val) => Err(EvalError::WrongBinOpArg(op, val))
    }
}

#[cfg(test)]
mod tests {
    use crate::{binding::ValueEnvironment, token::TokenStream, parse::parse};

    use super::*;

    /// Helper function for testing one evaluation. Will fail if the given 
    /// string fails to parse, or the evaluated value does not match 
    /// expectations.
    fn test_eval_helper<E: Environment>(s: &str, val: EvalResult<E>) {
        assert_eq!(
            evaluate(&parse(TokenStream::new(s.chars())).unwrap()),
            val
        );
    }

    #[test]
    fn test_evalute_int_constant() {
        test_eval_helper::<ValueEnvironment>("123", Ok(Value::Int(123)));
    }
}