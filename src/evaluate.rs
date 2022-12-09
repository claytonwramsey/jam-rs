use std::rc::Rc;

use crate::{
    ast::{Ast, BinOp, PrimFun, UnOp},
    binding::{BuildEnvironment, Environment},
    value::Value,
};

#[derive(Clone, Debug, PartialEq, Eq)]
/// The types of errors which can occur during a Jam interpretation.
pub enum Error<E: Environment> {
    /// A variable was unbound and occurred free.
    Unbound(String),
    /// The program attempted to call something which was not a function.
    NotAFunction(Value<E>),
    /// The program called a function with the wrong number of arguments.
    WrongArgCount { expected: usize, actual: usize },
    /// The wrong type was given as a parameter to a primitive function.
    WrongPrimArg(PrimFun, Value<E>),
    /// The wrong type was given to a binary operator.
    WrongBinOpArg(BinOp, Value<E>),
    /// The wrong value was given to a unary operator.
    WrongUnOpArg(UnOp, Value<E>),
    /// The condition to an if statement was not a bool.
    TestNonBool(Value<E>),
    /// A forward reference was created in a let statement.
    ForwardReference(String),
    /// Divide by zero was attempted.
    DivZero,
}

/// The result of an evaluation process.
pub type EvalResult<E> = Result<Value<E>, Error<E>>;

#[allow(unused)]
/// Evaluate a Jam expression. Returns the resulting value on success, and an
/// `Err` if the expression is incorrect in some way (typically due to type
/// errors).
pub fn evaluate<E: Environment + BuildEnvironment>(ast: &Ast) -> EvalResult<E> {
    eval_env(ast, E::build())
}

/// A helper function to evaluate a Jam expresion given a pre-existing
/// environment.
pub fn eval_env<E: Environment>(ast: &Ast, environment: Rc<E>) -> EvalResult<E> {
    let val = match ast {
        Ast::Int(n) => Value::Int(i64::from(*n)),
        Ast::Bool(b) => Value::Bool(*b),
        Ast::Empty => Value::List(Vec::new()),
        Ast::Variable(v) => environment.get(v)?,
        Ast::Primitive(f) => Value::Primitive(*f),
        Ast::App { rator, params } => {
            let resolved_rator = eval_env(rator, environment.clone())?;
            match resolved_rator {
                Value::Closure {
                    params: keys,
                    environment: closure_environment,
                    body,
                } => {
                    if params.len() != keys.len() {
                        return Err(Error::WrongArgCount {
                            expected: keys.len(),
                            actual: params.len(),
                        });
                    }
                    let new_env = closure_environment
                        .with(keys.iter().map(String::as_str).zip(params), environment)?;
                    eval_env(&body, new_env)?
                }
                Value::Primitive(f) => {
                    let mut args = Vec::new();
                    for param in params {
                        args.push(eval_env(param, environment.clone())?);
                    }
                    eval_primitive(f, &args)?
                }
                _ => return Err(Error::NotAFunction(resolved_rator)),
            }
        }
        Ast::BinOp { rator, lhs, rhs } => {
            let left_val = eval_env(lhs, environment.clone())?;
            let right_val = eval_env(rhs, environment)?;
            eval_binop(*rator, left_val, right_val)?
        }
        Ast::UnOp { rator, operand } => {
            let arg = eval_env(operand, environment)?;
            match rator {
                UnOp::Not => match arg {
                    Value::Bool(b) => Value::Bool(!b),
                    _ => return Err(Error::WrongUnOpArg(*rator, arg)),
                },
                UnOp::Neg => match arg {
                    Value::Int(x) => Value::Int(-x),
                    _ => return Err(Error::WrongUnOpArg(*rator, arg)),
                },
            }
        }
        Ast::If {
            condition,
            consequence,
            alternate,
        } => {
            let test_val = eval_env(condition, environment.clone())?;
            match test_val {
                Value::Bool(true) => eval_env(consequence, environment)?,
                Value::Bool(false) => eval_env(alternate, environment)?,
                _ => return Err(Error::TestNonBool(test_val)),
            }
        }
        Ast::Let { defs, body } => eval_env(
            body,
            environment.with_recursive(defs.iter().map(|(k, b)| (k.as_str(), b)))?,
        )?,
        Ast::Map { params, body } => Value::Closure {
            params: params.clone(),
            environment,
            body: body.clone(),
        },
    };
    // Useful message for debugging.
    // println!("[{ast}] -> [{val}]");
    Ok(val)
}

/// Evaluate a primitive function call. `args` is the values of all the
/// arguments to the function.
fn eval_primitive<E: Environment>(f: PrimFun, args: &[Value<E>]) -> EvalResult<E> {
    let require_param_len = |n| {
        if args.len() == n {
            Ok(())
        } else {
            Err(Error::WrongArgCount {
                expected: n,
                actual: args.len(),
            })
        }
    };
    Ok(match f {
        PrimFun::IsNumber => {
            require_param_len(1)?;
            Value::Bool(matches!(args[0], Value::Int(_)))
        }
        PrimFun::IsFunction => {
            require_param_len(1)?;
            Value::Bool(matches!(
                args[0],
                Value::Closure {
                    params: _,
                    environment: _,
                    body: _
                } | Value::Primitive(_)
            ))
        }
        PrimFun::IsList => {
            require_param_len(1)?;
            Value::Bool(matches!(args[0], Value::List(_)))
        }
        PrimFun::IsEmpty => {
            require_param_len(1)?;
            Value::Bool(args[0] == Value::List(Vec::new()))
        }
        PrimFun::IsCons => {
            require_param_len(1)?;
            Value::Bool(match &args[0] {
                Value::List(l) => !l.is_empty(),
                _ => false,
            })
        }
        PrimFun::Cons => {
            require_param_len(2)?;
            match args[1].clone() {
                Value::List(mut l) => {
                    let mut new_list = Vec::new();
                    new_list.append(&mut l);
                    new_list.push(args[0].clone());
                    Value::List(new_list)
                }
                a => return Err(Error::WrongPrimArg(f, a)),
            }
        }
        PrimFun::First => {
            require_param_len(1)?;
            match args[0].clone() {
                Value::List(l) => l
                    .last()
                    .ok_or_else(|| Error::WrongPrimArg(f, args[0].clone()))?
                    .clone(),
                a => return Err(Error::WrongPrimArg(f, a)),
            }
        }
        PrimFun::Rest => {
            require_param_len(1)?;
            match args[0].clone() {
                Value::List(mut l) => {
                    if l.is_empty() {
                        return Err(Error::WrongPrimArg(f, args[0].clone()));
                    }

                    l.pop();
                    Value::List(l)
                }
                a => return Err(Error::WrongPrimArg(f, a)),
            }
        }
        PrimFun::Arity => {
            require_param_len(1)?;
            match args[0].clone() {
                Value::Primitive(p) => Value::Int(match p {
                    PrimFun::Cons => 2,
                    _ => 1,
                }),
                Value::Closure {
                    params,
                    environment: _,
                    body: _,
                } => Value::Int(params.len() as i64),
                a => return Err(Error::WrongPrimArg(f, a)),
            }
        }
    })
}

/// Evaluate a binary operation `op`. Returns an error in case of a type error
/// or a divide by zero.
fn eval_binop<E: Environment>(op: BinOp, lhs: Value<E>, rhs: Value<E>) -> EvalResult<E> {
    Ok(match op {
        BinOp::Plus => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Int(a + b)
        }
        BinOp::Minus => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Int(a - b)
        }
        BinOp::Div => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            if b == 0 {
                return Err(Error::DivZero);
            }
            Value::Int(a / b)
        }
        BinOp::Mul => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Int(a * b)
        }
        BinOp::And => {
            let (a, b) = require_binop_bool(lhs, rhs, op)?;
            Value::Bool(a && b)
        }
        BinOp::Or => {
            let (a, b) = require_binop_bool(lhs, rhs, op)?;
            Value::Bool(a || b)
        }
        BinOp::Eq => Value::Bool(lhs == rhs),
        BinOp::Neq => Value::Bool(lhs != rhs),
        BinOp::Gt => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Bool(a > b)
        }
        BinOp::Geq => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Bool(a >= b)
        }
        BinOp::Lt => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Bool(a < b)
        }
        BinOp::Leq => {
            let (a, b) = require_binop_int(lhs, rhs, op)?;
            Value::Bool(a <= b)
        }
    })
}

/// Require that `lhs` and `rhs` be integers, or return an error if they are
/// not. Return the contained integers on `Ok()`.
fn require_binop_int<E: Environment>(
    lhs: Value<E>,
    rhs: Value<E>,
    op: BinOp,
) -> Result<(i64, i64), Error<E>> {
    match (lhs, rhs) {
        (Value::Int(a), Value::Int(b)) => Ok((a, b)),
        (val, Value::Int(_)) | (_, val) => Err(Error::WrongBinOpArg(op, val)),
    }
}

/// Require that `lhs` and `rhs` be booleans, or return an error if they are
/// not. Return the contained booleans on `Ok()`.
fn require_binop_bool<E: Environment>(
    lhs: Value<E>,
    rhs: Value<E>,
    op: BinOp,
) -> Result<(bool, bool), Error<E>> {
    match (lhs, rhs) {
        (Value::Bool(a), Value::Bool(b)) => Ok((a, b)),
        (val, Value::Bool(_)) | (_, val) => Err(Error::WrongBinOpArg(op, val)),
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        binding::{CallByName, CallByNeed, CallByValue},
        lex::TokenStream,
        parse::parse,
    };
    use std::fmt::Debug;

    use super::*;

    /// Helper function for testing one evaluation. Will fail if the given
    /// string fails to parse, or the evaluated value does not match
    /// expectations.
    fn test_eval_enver<E: Environment + Debug + BuildEnvironment>(s: &str, val: &EvalResult<E>) {
        assert_eq!(
            &evaluate::<E>(&parse(TokenStream::new(s.chars())).unwrap()),
            val
        );
    }

    #[test]
    fn test_evalute_int_constant() {
        test_eval_enver::<CallByValue>("123", &Ok(Value::Int(123)));
        test_eval_enver::<CallByName>("123", &Ok(Value::Int(123)));
        test_eval_enver::<CallByNeed>("123", &Ok(Value::Int(123)));
    }

    #[test]
    fn test_evaluate_let() {
        let s = "let a := 2; in a + a";
        test_eval_enver::<CallByValue>(s, &Ok(Value::Int(4)));
        test_eval_enver::<CallByName>(s, &Ok(Value::Int(4)));
        test_eval_enver::<CallByNeed>(s, &Ok(Value::Int(4)));
    }

    #[test]
    fn test_def_map_in_let() {
        let s = "let inc := map x to x + 1; in inc(4)";
        test_eval_enver::<CallByValue>(s, &Ok(Value::Int(5)));
        test_eval_enver::<CallByName>(s, &Ok(Value::Int(5)));
        test_eval_enver::<CallByNeed>(s, &Ok(Value::Int(5)));
    }

    #[test]
    fn test_branching() {
        let s = r#"
            let f := map x to 
                if list?(x) then 
                    if cons?(x) then 
                        first(x)
                    else 
                        empty 
                else x; 
            in 
                f(f(f(cons(cons(1, empty), empty))))
            "#;
        test_eval_enver::<CallByValue>(s, &Ok(Value::Int(1)));
        test_eval_enver::<CallByName>(s, &Ok(Value::Int(1)));
        test_eval_enver::<CallByNeed>(s, &Ok(Value::Int(1)));
    }

    #[test]
    fn test_y() {
        let s = r#"
            let 
                Y := map f to 
                    let 
                        g := map x to f(x(x));
                    in 
                        g(g);
                fact := map f to 
                    map n to 
                        if n = 0 then
                            1
                        else
                            n * f(n - 1);
            in 
                (Y(fact))(6)
        "#;
        test_eval_enver::<CallByName>(s, &Ok(Value::Int(720)));
        test_eval_enver::<CallByNeed>(s, &Ok(Value::Int(720)));
    }

    #[test]
    fn test_recursion() {
        let s = r#"
            let 
                fact := map n to
                    if n = 0 then
                        1
                    else
                        n * fact(n - 1);
            in
                fact(6)
        "#;
        test_eval_enver::<CallByValue>(s, &Ok(Value::Int(720)));
        test_eval_enver::<CallByName>(s, &Ok(Value::Int(720)));
        test_eval_enver::<CallByNeed>(s, &Ok(Value::Int(720)));
    }

    #[test]
    fn test_fib() {
        let s = r#"
            let
                fib := map n to 
                    if n = 0 then 0
                    else if n = 1 then 1
                    else fib(n - 1) + fib(n - 2);
            in
                fib(20)
        "#;
        test_eval_enver::<CallByValue>(s, &Ok(Value::Int(6765)));
        test_eval_enver::<CallByName>(s, &Ok(Value::Int(6765)));
        test_eval_enver::<CallByNeed>(s, &Ok(Value::Int(6765)));
    }

    #[test]
    fn test_list_fib() {
        let s = r#"
            let 
                fib_next := map l to cons(first(l) + first(rest(l)), l);
                fib_help := map n to 
                    if n = 1 then cons(1, cons(0, empty))
                    else if n = 0 then cons(0, empty)
                    else fib_next(fib_help(n - 1));
                fib := map n to first(fib_help(n));
            in 
                fib(10)
        "#;
        test_eval_enver::<CallByValue>(s, &Ok(Value::Int(55)));
        test_eval_enver::<CallByName>(s, &Ok(Value::Int(55)));
        test_eval_enver::<CallByNeed>(s, &Ok(Value::Int(55)));
    }

    #[test]
    fn equal_closures() {
        let s = r#"
            let 
                c1 := map l to l + 1;
                c2 := map l to l + 1;
            in 
                c1 = c2
        "#;
        test_eval_enver::<CallByValue>(s, &Ok(Value::Bool(true)));
        test_eval_enver::<CallByName>(s, &Ok(Value::Bool(true)));
        test_eval_enver::<CallByNeed>(s, &Ok(Value::Bool(true)));
    }
}
