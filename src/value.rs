//! A module for the values which can be returned from a Jam program.
//! Eventually, part of this module will be split out for the behavior of
//! `cons`.

use std::{
    borrow::Borrow,
    fmt::{self, Display},
    rc::{Rc, Weak},
};

use crate::{
    ast::{write_list, Ast, PrimFun},
    binding::Environment,
};

#[derive(Debug, PartialEq, Eq)]
/// The return value of a Jam program.
pub enum Value<E: Environment> {
    /// A signed integer.
    Int(i64),
    /// A boolean.
    Bool(bool),
    /// A list.
    List(Vec<Value<E>>),
    /// A function, with a body which has not been evaluated yet.
    Closure {
        params: Vec<String>,
        environment: Rc<E>,
        body: Rc<Ast>,
    },
    /// A primitive function.
    Primitive(PrimFun),
}

#[derive(Clone, Debug)]
#[allow(clippy::module_name_repetitions)]
/// A Jam value which can potentially contain weak references to its definition
/// environments.
pub enum EitherValue<E: Environment> {
    /// A signed integer.
    Int(i64),
    /// A boolean.
    Bool(bool),
    /// A list.
    List(Vec<Rc<EitherValue<E>>>),
    /// A closure with strong references to its definition environment.
    StrongClosure {
        params: Vec<String>,
        environment: Rc<E>,
        body: Rc<Ast>,
    },
    /// A closure with weak references to its definition environment.
    WeakClosure {
        params: Vec<String>,
        environment: Weak<E>,
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
pub fn demote_in<E: Environment>(ev: &Rc<EitherValue<E>>, env: &E) -> Rc<EitherValue<E>> {
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
            if std::ptr::eq(environment.as_ref() as *const E, env as *const E) {
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
pub fn strengthen<E: Environment>(ev: &Rc<EitherValue<E>>) -> Rc<EitherValue<E>> {
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

impl<E: Environment> EitherValue<E> {
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
    fn strongly_refers_to(&self, env: &E) -> bool {
        match self {
            EitherValue::List(l) => l.iter().any(|val| val.strongly_refers_to(env)),
            EitherValue::StrongClosure {
                params: _,
                environment,
                body: _,
            } => std::ptr::eq(environment.as_ref() as *const E, env as *const E),
            _ => false,
        }
    }
}

impl<E, T> From<T> for Value<E>
where
    E: Environment,
    T: Borrow<EitherValue<E>>,
{
    /// Convert an `EitherValue` into a strong `Value`, upgrading any
    /// references along the way.
    ///
    /// # Panics
    ///
    /// Will panic if a weak reference to an environment has expired.
    fn from(ev: T) -> Self {
        match ev.borrow() {
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

impl<T, E> From<T> for EitherValue<E>
where
    E: Environment,
    T: Borrow<Value<E>>,
{
    /// Construct an `EitherValue`, using a strong reference for each closure.
    fn from(value: T) -> Self {
        match value.borrow() {
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

impl<E: Environment> PartialEq for EitherValue<E> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Int(l0), Self::Int(r0)) => l0 == r0,
            (Self::Bool(l0), Self::Bool(r0)) => l0 == r0,
            (Self::List(l0), Self::List(r0)) => l0 == r0,
            (
                Self::StrongClosure {
                    params: l_params,
                    environment: l_environment,
                    body: l_body,
                },
                Self::StrongClosure {
                    params: r_params,
                    environment: r_environment,
                    body: r_body,
                },
            ) => l_params == r_params && l_environment == r_environment && l_body == r_body,
            (
                Self::WeakClosure {
                    params: l_params,
                    environment: l_environment,
                    body: l_body,
                },
                Self::WeakClosure {
                    params: r_params,
                    environment: r_environment,
                    body: r_body,
                },
            ) => {
                l_params == r_params
                    && l_environment.upgrade().unwrap() == r_environment.upgrade().unwrap()
                    && l_body == r_body
            }
            (Self::Primitive(l0), Self::Primitive(r0)) => l0 == r0,
            _ => false,
        }
    }
}

impl<E: Environment> Eq for EitherValue<E> {}

impl<E: Environment> Display for Value<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{i}"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::List(l) => {
                write!(f, "(")?;
                let mut iter = l.iter().rev();
                match (iter.next(), iter.next()) {
                    (None, _) => (),
                    (Some(v), None) => {
                        write!(f, "{v}")?;
                    }
                    (Some(v1), Some(v2)) => {
                        write!(f, "{v1}, {v2}")?;
                        for value in iter {
                            write!(f, ", {value}")?;
                        }
                    }
                };
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

impl<E: Environment> Clone for Value<E> {
    fn clone(&self) -> Self {
        match self {
            Self::Int(arg0) => Self::Int(*arg0),
            Self::Bool(arg0) => Self::Bool(*arg0),
            Self::List(arg0) => Self::List(arg0.clone()),
            Self::Closure {
                params,
                environment,
                body,
            } => Self::Closure {
                params: params.clone(),
                environment: environment.clone(),
                body: body.clone(),
            },
            Self::Primitive(arg0) => Self::Primitive(*arg0),
        }
    }
}
