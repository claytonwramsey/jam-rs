//! A module for the values which can be returned from a Jam program.
//! Eventually, part of this module will be split out for the behavior of
//! `cons`.

use std::{
    borrow::Borrow,
    collections::LinkedList,
    fmt::{self, Display},
    rc::{Rc, Weak},
};

use crate::{
    ast::{write_list, Ast, PrimFun},
    binding::Environment,
};

#[derive(Clone, Debug, Eq)]
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
    List(LinkedList<Rc<EitherValue>>),
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

/// Creates a version of this value, where, if it was previously a strong
/// value pointing to the given environment, promotes it.
///
/// # Panics
///
/// Will panic if the environment requested for promotion no longer exists.
pub fn demote_in(ev: &Rc<EitherValue>, env: &dyn Environment) -> Rc<EitherValue> {
    match ev.borrow() {
        EitherValue::List(l) => {
            // don't bother demoting anything if we don't need to
            if ev.strongly_refers_to(env) {
                Rc::new(EitherValue::List(
                    l.iter().map(|val| demote_in(val, env)).collect(),
                ))
            } else {
                ev.clone()
            }
        }
        EitherValue::StrongClosure {
            params,
            environment,
            body,
        } => {
            if std::ptr::eq(
                environment.as_ref() as *const dyn Environment as *const u8,
                env as *const dyn Environment as *const u8,
            ) {
                Rc::new(EitherValue::WeakClosure {
                    params: params.clone(),
                    environment: Rc::downgrade(environment),
                    body: body.clone(),
                })
            } else {
                ev.clone()
            }
        }
        _ => ev.clone(),
    }
}

/// Convert this value to one which has no `WeakClosure`s. Will have no effect
/// if there were no weak closures to begin with, yielding the original Rc.
pub fn strengthen(ev: &Rc<EitherValue>) -> Rc<EitherValue> {
    match ev.borrow() {
        EitherValue::List(l) => {
            if l.iter().all(|val| val.is_strong()) {
                // if all children are strong, reuse this value
                ev.clone()
            } else {
                Rc::new(EitherValue::List(l.iter().map(strengthen).collect()))
            }
        }
        EitherValue::WeakClosure {
            params,
            environment,
            body,
        } => Rc::new(EitherValue::StrongClosure {
            params: params.clone(),
            environment: environment.upgrade().unwrap(), // might panic
            body: body.clone(),
        }),
        _ => ev.clone(),
    }
}

impl EitherValue {
    /// Determine whether all closures in this either value are strong. If
    /// there is one weak closure, this value is not strong.
    fn is_strong(&self) -> bool {
        match self {
            EitherValue::List(l) => l.iter().all(|ev| ev.is_strong()),
            EitherValue::WeakClosure {
                params: _,
                environment: _,
                body: _,
            } => false,
            _ => true,
        }
    }

    /// Determine whether this value strongly refers to a given environment.
    fn strongly_refers_to(&self, env: &dyn Environment) -> bool {
        match self {
            EitherValue::List(l) => l.iter().any(|val| val.strongly_refers_to(env)),
            EitherValue::StrongClosure {
                params: _,
                environment,
                body: _,
            } => std::ptr::eq(
                environment.as_ref() as *const dyn Environment as *const u8,
                env as *const dyn Environment as *const u8,
            ),
            _ => false,
        }
    }
}

impl From<&EitherValue> for Value {
    /// Convert an `EitherValue` into a strong `Value`, upgrading any
    /// references along the way.
    ///
    /// # Panics
    ///
    /// Will panic if a weak reference to an environment has expired.
    fn from(ev: &EitherValue) -> Self {
        match ev {
            EitherValue::Int(i) => Value::Int(*i),
            EitherValue::Bool(b) => Value::Bool(*b),
            EitherValue::List(l) => {
                Value::List(l.iter().map(|either| either.as_ref().into()).collect())
            }
            EitherValue::StrongClosure {
                params,
                environment,
                body,
            } => Value::Closure {
                params: params.clone(),
                environment: environment.clone(),
                body: body.clone(),
            },
            EitherValue::WeakClosure {
                params,
                environment,
                body,
            } => Value::Closure {
                params: params.clone(),
                environment: environment.upgrade().unwrap(), // might panic
                body: body.clone(),
            },
            EitherValue::Primitive(f) => Value::Primitive(*f),
        }
    }
}

impl<T> From<T> for Value
where
    T: AsRef<EitherValue>,
{
    fn from(r: T) -> Self {
        r.as_ref().into()
    }
}

impl From<EitherValue> for Value {
    fn from(ev: EitherValue) -> Self {
        (&ev).into()
    }
}

impl From<&Value> for EitherValue {
    /// Construct an `EitherValue`, using a strong reference for each closure.
    fn from(value: &Value) -> Self {
        match value {
            Value::Int(i) => EitherValue::Int(*i),
            Value::Bool(b) => EitherValue::Bool(*b),
            Value::List(l) => {
                EitherValue::List(l.iter().map(|item| Rc::new(item.into())).collect())
            }
            Value::Closure {
                params,
                environment,
                body,
            } => EitherValue::StrongClosure {
                params: params.clone(),
                environment: environment.clone(),
                body: body.clone(),
            },
            Value::Primitive(f) => EitherValue::Primitive(*f),
        }
    }
}

impl From<Value> for EitherValue {
    fn from(value: Value) -> Self {
        (&value).into()
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
