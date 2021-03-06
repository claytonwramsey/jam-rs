use std::{collections::LinkedList, rc::Rc};

use crate::{
    ast::{Ast, BinOp, PrimFun, UnOp},
    binding::{BuildEnvironment, Environment},
    value::Value,
};

#[derive(Clone, Debug, PartialEq, Eq)]
/// The types of errors which can occur during a Jam interpretation.
pub enum EvalError {
    /// A variable was unbound and occurred free.
    Unbound(String),
    /// The program attempted to call something which was not a function.
    NotAFunction(Value),
    /// The program called a function with the wrong number of arguments.
    WrongArgCount { expected: usize, actual: usize },
    /// The wrong type was given as a parameter to a primitive function.
    WrongPrimArg(PrimFun, Value),
    /// The wrong type was given to a binary operator.
    WrongBinOpArg(BinOp, Value),
    /// The wrong value was given to a unary operator.
    WrongUnOpArg(UnOp, Value),
    /// The condition to an if statement was not a bool.
    TestNonBool(Value),
    /// A forward reference was created in a let statement.
    ForwardReference(String),
    /// Divide by zero was attempted.
    DivZero,
}

/// The result of an evaluation process.
pub type EvalResult = Result<Value, EvalError>;

#[allow(unused)]
/// Evaluate a Jam expression. Returns the resulting value on success, and an
/// `Err` if the expression is incorrect in some way (typically due to type
/// errors).
pub fn evaluate<E: 'static + BuildEnvironment>(ast: &Ast) -> EvalResult {
    evaluate_help(ast, E::build())
}

/// A helper function to evaluate a Jam expresion given a pre-existing
/// environment.
pub fn evaluate_help(ast: &Ast, environment: Rc<dyn Environment>) -> EvalResult {
    let val = match ast {
        Ast::Int(n) => Value::Int(*n as i32),
        Ast::Bool(b) => Value::Bool(*b),
        Ast::Empty => Value::List(LinkedList::new()),
        Ast::Variable(v) => environment.get(v)?,
        Ast::Primitive(f) => Value::Primitive(*f),
        Ast::App { rator, params } => {
            let resolved_rator = evaluate_help(rator, environment.clone())?;
            match resolved_rator {
                Value::Closure {
                    params: keys,
                    environment: closure_environment,
                    body,
                } => {
                    if params.len() != keys.len() {
                        return Err(EvalError::WrongArgCount {
                            expected: keys.len(),
                            actual: params.len(),
                        });
                    }
                    let new_env = closure_environment
                        .with(&mut keys.iter().zip(params.iter()), environment)?;
                    evaluate_help(&body, new_env)?
                }
                Value::Primitive(f) => {
                    let mut args = Vec::new();
                    for param in params {
                        args.push(evaluate_help(param, environment.clone())?);
                    }
                    eval_primitive(f, args)?
                }
                _ => return Err(EvalError::NotAFunction(resolved_rator)),
            }
        }
        Ast::BinOp { rator, lhs, rhs } => {
            let lval = evaluate_help(lhs, environment.clone())?;
            let rval = evaluate_help(rhs, environment)?;
            eval_binop(*rator, lval, rval)?
        }
        Ast::UnOp { rator, operand } => {
            let arg = evaluate_help(operand, environment)?;
            match rator {
                UnOp::Not => match arg {
                    Value::Bool(b) => Value::Bool(!b),
                    _ => return Err(EvalError::WrongUnOpArg(*rator, arg)),
                },
                UnOp::Neg => match arg {
                    Value::Int(x) => Value::Int(-x),
                    _ => return Err(EvalError::WrongUnOpArg(*rator, arg)),
                },
            }
        }
        Ast::If {
            condition,
            consequence,
            alternate,
        } => {
            let test_val = evaluate_help(condition, environment.clone())?;
            match test_val {
                Value::Bool(true) => evaluate_help(consequence, environment.clone())?,
                Value::Bool(false) => evaluate_help(alternate, environment)?,
                _ => return Err(EvalError::TestNonBool(test_val)),
            }
        }
        Ast::Let { defs, body } => evaluate_help(
            body,
            environment.with_recursive(&mut defs.iter().map(|(k, b)| (k, b)))?,
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
fn eval_primitive(f: PrimFun, args: Vec<Value>) -> EvalResult {
    let require_param_len = |n| match args.len() == n {
        true => Ok(()),
        false => Err(EvalError::WrongArgCount {
            expected: n,
            actual: args.len(),
        }),
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
            Value::Bool(args[0] == Value::List(LinkedList::new()))
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
            match args[1].to_owned() {
                Value::List(mut l) => {
                    let mut new_list = LinkedList::new();
                    new_list.append(&mut l);
                    new_list.push_front(args[0].to_owned());
                    Value::List(new_list)
                }
                a => return Err(EvalError::WrongPrimArg(f, a)),
            }
        }
        PrimFun::First => {
            require_param_len(1)?;
            match args[0].to_owned() {
                Value::List(l) => l
                    .front()
                    .ok_or_else(|| EvalError::WrongPrimArg(f, args[0].clone()))?
                    .clone(),
                a => return Err(EvalError::WrongPrimArg(f, a)),
            }
        }
        PrimFun::Rest => {
            require_param_len(1)?;
            match args[0].to_owned() {
                Value::List(mut l) => {
                    if l.is_empty() {
                        return Err(EvalError::WrongPrimArg(f, args[0].clone()));
                    } else {
                        l.pop_front();
                        Value::List(l)
                    }
                }
                a => return Err(EvalError::WrongPrimArg(f, a)),
            }
        }
        PrimFun::Arity => {
            require_param_len(1)?;
            match args[0].to_owned() {
                Value::Primitive(p) => Value::Int(match p {
                    PrimFun::Cons => 2,
                    _ => 1,
                }),
                Value::Closure {
                    params,
                    environment: _,
                    body: _,
                } => Value::Int(params.len() as i32),
                a => return Err(EvalError::WrongPrimArg(f, a)),
            }
        }
    })
}

/// Evaluate a binary operation `op`. Returns an error in case of a type error
/// or a divide by zero.
fn eval_binop(op: BinOp, lhs: Value, rhs: Value) -> EvalResult {
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
                return Err(EvalError::DivZero);
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
fn require_binop_int(lhs: Value, rhs: Value, op: BinOp) -> Result<(i32, i32), EvalError> {
    match (lhs, rhs) {
        (Value::Int(a), Value::Int(b)) => Ok((a, b)),
        (val, Value::Int(_)) => Err(EvalError::WrongBinOpArg(op, val)),
        (_, val) => Err(EvalError::WrongBinOpArg(op, val)),
    }
}

/// Require that `lhs` and `rhs` be booleans, or return an error if they are
/// not. Return the contained booleans on `Ok()`.
fn require_binop_bool(lhs: Value, rhs: Value, op: BinOp) -> Result<(bool, bool), EvalError> {
    match (lhs, rhs) {
        (Value::Bool(a), Value::Bool(b)) => Ok((a, b)),
        (val, Value::Bool(_)) => Err(EvalError::WrongBinOpArg(op, val)),
        (_, val) => Err(EvalError::WrongBinOpArg(op, val)),
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        binding::{CallByName, CallByNeed, CallByValue},
        parse::parse,
        token::TokenStream,
    };

    use super::*;

    /// Helper function for testing one evaluation. Will fail if the given
    /// string fails to parse, or the evaluated value does not match
    /// expectations.
    fn test_eval_helper<E: 'static + BuildEnvironment>(s: &str, val: EvalResult) {
        assert_eq!(
            evaluate::<E>(&parse(TokenStream::new(s.chars())).unwrap()),
            val
        );
    }

    #[test]
    fn test_evalute_int_constant() {
        test_eval_helper::<CallByValue>("123", Ok(Value::Int(123)));
        test_eval_helper::<CallByName>("123", Ok(Value::Int(123)));
        test_eval_helper::<CallByNeed>("123", Ok(Value::Int(123)));
    }

    #[test]
    fn test_evaluate_let() {
        let s = "let a := 2; in a + a";
        test_eval_helper::<CallByValue>(s, Ok(Value::Int(4)));
        test_eval_helper::<CallByName>(s, Ok(Value::Int(4)));
        test_eval_helper::<CallByNeed>(s, Ok(Value::Int(4)));
    }

    #[test]
    fn test_def_map_in_let() {
        let s = "let inc := map x to x + 1; in inc(4)";
        test_eval_helper::<CallByValue>(s, Ok(Value::Int(5)));
        test_eval_helper::<CallByName>(s, Ok(Value::Int(5)));
        test_eval_helper::<CallByNeed>(s, Ok(Value::Int(5)));
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
        test_eval_helper::<CallByValue>(s, Ok(Value::Int(1)));
        test_eval_helper::<CallByName>(s, Ok(Value::Int(1)));
        test_eval_helper::<CallByNeed>(s, Ok(Value::Int(1)));
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
        test_eval_helper::<CallByName>(s, Ok(Value::Int(720)));
        test_eval_helper::<CallByNeed>(s, Ok(Value::Int(720)));
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
        test_eval_helper::<CallByValue>(s, Ok(Value::Int(720)));
        test_eval_helper::<CallByName>(s, Ok(Value::Int(720)));
        test_eval_helper::<CallByNeed>(s, Ok(Value::Int(720)));
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
        test_eval_helper::<CallByValue>(s, Ok(Value::Int(6765)));
        test_eval_helper::<CallByName>(s, Ok(Value::Int(6765)));
        test_eval_helper::<CallByNeed>(s, Ok(Value::Int(6765)));
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
        test_eval_helper::<CallByValue>(s, Ok(Value::Int(55)));
        test_eval_helper::<CallByName>(s, Ok(Value::Int(55)));
        test_eval_helper::<CallByNeed>(s, Ok(Value::Int(55)));
    }
}
