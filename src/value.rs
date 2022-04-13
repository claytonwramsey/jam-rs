//! A module for the values which can be returned from a Jam program.
//! Eventually, part of this module will be split out for the behavior of
//! `cons`.

use std::{
    collections::LinkedList,
    fmt::{self, Display},
    rc::{Rc, Weak},
};

use crate::{
    ast::{write_list, Ast, PrimFun},
    binding::{is_same, Environment},
};

#[derive(Clone, Debug)]
/// The return value of a Jam program.
pub enum Value {
    /// A signed integer.
    Int(i32),
    /// A boolean.
    Bool(bool),
    /// A list.
    List(LinkedList<Value>),
    /// A function, with a body which has not been evaluated yet.
    Closure {
        params: Vec<String>,
        environment: Rc<dyn Environment>,
        body: Rc<Ast>,
    },
    /// A primitive function.
    Primitive(PrimFun),
}

#[derive(Clone, Debug)]
/// A Jam value which can potentially contain weak references to its definition
/// environments.
pub enum EitherValue {
    /// A signed integer.
    Int(i32),
    /// A boolean.
    Bool(bool),
    /// A list.
    List(LinkedList<EitherValue>),
    /// A closure with strong references to its definition environment.
    StrongClosure {
        params: Vec<String>,
        environment: Rc<dyn Environment>,
        body: Rc<Ast>,
    },
    /// A closure with weak references to its definition environment.
    WeakClosure {
        params: Vec<String>,
        environment: Weak<dyn Environment>,
        body: Rc<Ast>,
    },
    /// A primitive function.
    Primitive(PrimFun),
}

impl EitherValue {
    /// Convert this value to one which only uses `StrongClosure`s.
    pub fn as_strong(&self) -> EitherValue {
        match self {
            EitherValue::List(l) => {
                EitherValue::List(l.iter().map(|either| either.as_strong()).collect())
            }
            EitherValue::WeakClosure {
                params,
                environment,
                body,
            } => EitherValue::StrongClosure {
                params: params.clone(),
                environment: environment.upgrade().unwrap(), // might panic
                body: body.clone(),
            },
            _ => self.clone(),
        }
    }

    /// Creates a version of this value where all strong references have been
    /// demoted. May cause a panic in the future if the weak references in this
    /// value are the last reference to their environment.
    pub fn as_weak(&self) -> EitherValue {
        match self {
            EitherValue::List(l) => {
                EitherValue::List(l.iter().map(|either| either.as_weak()).collect())
            }
            EitherValue::StrongClosure {
                params,
                environment,
                body,
            } => EitherValue::WeakClosure {
                params: params.clone(),
                environment: Rc::downgrade(environment),
                body: body.clone(),
            },
            _ => self.clone(),
        }
    }

    /// Creates a version of this value, where, if it was previously a strong
    /// value pointing to the given environment, promotes it.
    ///
    /// # Panics
    ///
    /// Will panic if the environment requested for promotion no longer exists.
    pub fn demote_in(&self, env: Rc<dyn Environment>) -> EitherValue {
        match self {
            EitherValue::List(l) => EitherValue::List(
                l.iter()
                    .map(|either| either.demote_in(env.clone()))
                    .collect(),
            ),
            EitherValue::StrongClosure {
                params: _,
                environment,
                body: _,
            } => {
                if is_same(env.as_ref(), environment.as_ref()) {
                    println!("weakening!");
                    self.as_weak()
                } else {
                    println!("maintaining strength!");
                    self.clone()
                }
            }
            _ => self.clone(),
        }
    }
}

impl From<EitherValue> for Value {
    /// Convert an `EitherValue` into a strong `Value`, upgrading any
    /// references along the way.
    ///
    /// # Panics
    ///
    /// Will panic if a weak reference to an environment has expired.
    fn from(ev: EitherValue) -> Self {
        match ev {
            EitherValue::Int(i) => Value::Int(i),
            EitherValue::Bool(b) => Value::Bool(b),
            EitherValue::List(l) => {
                Value::List(l.into_iter().map(|either| either.into()).collect())
            }
            EitherValue::StrongClosure {
                params,
                environment,
                body,
            } => Value::Closure {
                params,
                environment,
                body,
            },
            EitherValue::WeakClosure {
                params,
                environment,
                body,
            } => Value::Closure {
                params,
                environment: environment.upgrade().unwrap(), // might panic
                body,
            },
            EitherValue::Primitive(f) => Value::Primitive(f),
        }
    }
}

impl From<Value> for EitherValue {
    /// Construct an `EitherValue`, using a strong reference for each closure.
    fn from(value: Value) -> Self {
        match value {
            Value::Int(i) => EitherValue::Int(i),
            Value::Bool(b) => EitherValue::Bool(b),
            Value::List(l) => EitherValue::List(l.into_iter().map(|item| item.into()).collect()),
            Value::Closure {
                params,
                environment,
                body,
            } => EitherValue::StrongClosure {
                params,
                environment,
                body,
            },
            Value::Primitive(f) => EitherValue::Primitive(f),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Int(l0), Self::Int(r0)) => l0 == r0,
            (Self::Bool(l0), Self::Bool(r0)) => l0 == r0,
            (Self::List(l0), Self::List(r0)) => l0 == r0,
            (
                Self::Closure {
                    params: l_params,
                    environment: l_environment,
                    body: l_body,
                },
                Self::Closure {
                    params: r_params,
                    environment: r_environment,
                    body: r_body,
                },
            ) => l_params == r_params && l_environment == r_environment && l_body == r_body,
            (Self::Primitive(l0), Self::Primitive(r0)) => l0 == r0,
            _ => false,
        }
    }
}

impl Eq for Value {}

impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{i}"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::List(l) => {
                write!(f, "(")?;
                let vals: Vec<Value> = l.iter().cloned().collect();
                write_list(&vals, " ", f)?;
                write!(f, ")")
            }
            Value::Closure {
                params,
                environment: _,
                body,
            } => {
                write!(f, "(closure: ")?;
                write_list(params, ", ", f)?;
                write!(f, "-> {body}")
            }
            Value::Primitive(fun) => write!(f, "{fun}"),
        }
    }
}
