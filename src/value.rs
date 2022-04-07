//! A module for the values which can be returned from a Jam program. 
//! Eventually, part of this module will be split out for the behavior of 
//! `cons`.

use std::rc::Rc;

use crate::{
    ast::{Ast, PrimFun},
    binding::Environment,
};

#[derive(Clone, Debug)]
/// The return value of a Jam program.
pub enum Value {
    /// A signed integer.
    Int(i32),
    /// A boolean.
    Bool(bool),
    /// A list.
    List(ListVal),
    /// A function, with a body which has not been evaluated yet.
    Closure {
        params: Vec<String>,
        environment: Rc<dyn Environment>,
        body: Rc<Ast>,
    },
    /// A primitive function.
    Primitive(PrimFun),
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

#[derive(Clone, Debug, PartialEq, Eq)]
/// A value which is a list. 
pub enum ListVal {
    /// A constructed list.
    Cons { head: Rc<Value>, tail: Rc<ListVal> },
    /// The empty list.
    Empty,
}
