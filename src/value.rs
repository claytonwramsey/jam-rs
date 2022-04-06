use std::rc::Rc;

use crate::{binding::Environment, ast::{Ast, PrimFun}};


#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value<E: Environment> {
    Int(i32),
    Bool(bool),
    List(ListVal<E>),
    Closure {
        params: Vec<String>,
        environment: E,
        body: Rc::<Ast>,
    },
    Primitive(PrimFun),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ListVal<E: Environment> {
    Cons {
        head: Rc<Value<E>>,
        tail: Rc<ListVal<E>>,
    },
    Empty
}