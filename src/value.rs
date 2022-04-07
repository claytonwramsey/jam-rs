use std::rc::Rc;

use crate::{
    ast::{Ast, PrimFun},
    binding::Environment,
};

#[derive(Clone, Debug)]
pub enum Value {
    Int(i32),
    Bool(bool),
    List(ListVal),
    Closure {
        params: Vec<String>,
        environment: Rc<dyn Environment>,
        body: Rc<Ast>,
    },
    Primitive(PrimFun),
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Int(l0), Self::Int(r0)) => l0 == r0,
            (Self::Bool(l0), Self::Bool(r0)) => l0 == r0,
            (Self::List(l0), Self::List(r0)) => l0 == r0,
            (Self::Closure { params: l_params, environment: l_environment, body: l_body }, Self::Closure { params: r_params, environment: r_environment, body: r_body }) => l_params == r_params && l_environment == r_environment && l_body == r_body,
            (Self::Primitive(l0), Self::Primitive(r0)) => l0 == r0,
            _ => false,
        }
    }
}

impl Eq for Value {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ListVal {
    Cons { head: Rc<Value>, tail: Rc<ListVal> },
    Empty,
}
