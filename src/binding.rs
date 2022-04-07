//! A module for environments and binding rules. Contains implementations for 
//! call-by-need, call-by-name, and call-by-value, as well as the traits 
//! required to implement a custom binding scheme.

use std::{cell::RefCell, collections::HashMap, fmt::Debug, rc::Rc};

use crate::{
    ast::Ast,
    evaluate::{evaluate_help, EvalError, EvalResult},
    value::Value,
};

pub trait BuildEnvironment: Environment + Default {}

/// An environment is a structure which can be used to store and retrieve
/// values. Environments must be able to be cloned and compared for equality to
/// assist in the creation of maps. The default value of an environment will
/// always be an "empty" environment with no bindings.
pub trait Environment: Debug {
    /// Get the set of keys for this environment.
    fn keys(&self) -> Box<dyn Iterator<Item = String>>;

    /// Create a new environment with the same properties as the original one.
    fn duplicate(&self) -> Box<dyn Environment>;

    /// Store a key in the environment. The context is the environment that the
    /// key was created in.
    fn store(
        &mut self,
        context: Rc<dyn Environment>,
        key: &String,
        body: &Ast,
    ) -> Result<(), EvalError>;

    /// Get the key from an environment. Returns an unbound error if it is
    /// unable to get the key. Although the pointer to `self` is mutable, the
    /// environment may not remove any bindings - this is for call-by-need.
    fn get(&self, key: &String) -> EvalResult;
}

impl PartialEq for dyn Environment {
    fn eq(&self, other: &Self) -> bool {
        for k1 in self.keys() {
            let v1 = self.get(&k1);
            let v2 = other.get(&k1);

            if v2 != v1 {
                return false;
            }
        }

        for k2 in self.keys() {
            let v1 = self.get(&k2);
            let v2 = other.get(&k2);

            if v2 != v1 {
                return false;
            }
        }

        true
    }
}

impl Eq for dyn Environment {}

/* Call-by-value */

#[derive(Clone, Debug, PartialEq, Eq)]
/// An environment for call-by-value.
pub struct CallByValue {
    /// The stored key-value pairs.
    storage: HashMap<String, Value>,
}

impl Environment for CallByValue {
    fn duplicate(&self) -> Box<dyn Environment> {
        Box::new(self.clone())
    }

    fn keys(&self) -> Box<dyn Iterator<Item = String>> {
        Box::new(
            self.storage
                .keys()
                .map(|s| s.clone())
                .collect::<Vec<String>>()
                .into_iter(),
        )
    }

    /// Store a value. Will eagerly evaluate the body to get the resulting
    /// value.
    fn store(
        &mut self,
        context: Rc<dyn Environment>,
        key: &String,
        body: &Ast,
    ) -> Result<(), EvalError> {
        self.storage
            .insert(key.clone(), evaluate_help(&body, context)?);

        Ok(())
    }

    /// Get a key
    fn get(&self, key: &String) -> EvalResult {
        Ok(self
            .storage
            .get(key)
            .ok_or(EvalError::Unbound(key.clone()))?
            .clone())
    }
}

impl Default for CallByValue {
    fn default() -> CallByValue {
        CallByValue {
            storage: HashMap::new(),
        }
    }
}

impl BuildEnvironment for CallByValue {}

/* Call-by-name */

#[derive(Clone, Debug, PartialEq, Eq)]
/// A call-by-name environment.
pub struct CallByName {
    /// map from variables to the ASTs they represent
    storage: HashMap<String, (Rc<dyn Environment>, Ast)>,
}

impl Environment for CallByName {
    fn store(
        &mut self,
        context: Rc<dyn Environment>,
        key: &String,
        body: &Ast,
    ) -> Result<(), EvalError> {
        self.storage
            .insert(key.clone(), (context.clone(), body.clone()));

        Ok(())
    }

    fn get(&self, key: &String) -> EvalResult {
        let (env, body) = self
            .storage
            .get(key)
            .ok_or(EvalError::Unbound(key.clone()))?;
        evaluate_help(body, env.clone())
    }

    fn keys(&self) -> Box<dyn Iterator<Item = String>> {
        Box::new(
            self.storage
                .keys()
                .map(|s| s.clone())
                .collect::<Vec<String>>()
                .into_iter(),
        )
    }

    fn duplicate(&self) -> Box<dyn Environment> {
        Box::new(self.clone())
    }
}

impl Default for CallByName {
    fn default() -> CallByName {
        CallByName {
            storage: HashMap::new(),
        }
    }
}

impl BuildEnvironment for CallByName {}

/* Call-by-need. */

#[derive(Clone, Debug)]
/// The internal values of bindings in a call-by-need environment.
enum NeedValue {
    /// The value has not yet been evaluated.
    Ast(Rc<dyn Environment>, Ast),
    /// The value has been evaluated.
    Value(Value),
}

impl PartialEq for NeedValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Ast(l0, l1), Self::Ast(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::Value(l0), Self::Value(r0)) => l0 == r0,
            _ => false,
        }
    }
}

impl Eq for NeedValue {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallByNeed {
    storage: HashMap<String, RefCell<NeedValue>>,
}

impl Environment for CallByNeed {
    fn store(
        &mut self,
        context: Rc<dyn Environment>,
        key: &String,
        body: &Ast,
    ) -> Result<(), EvalError> {
        self.storage.insert(
            key.clone(),
            RefCell::new(NeedValue::Ast(context.clone(), body.clone())),
        );

        Ok(())
    }

    fn get(&self, key: &String) -> EvalResult {
        match self.storage.get(key) {
            Some(cell) => {
                let value;
                match &*cell.borrow() {
                    NeedValue::Ast(env, ast) => value = evaluate_help(&ast, env.clone())?,
                    NeedValue::Value(val) => return Ok(val.clone()),
                };
                cell.replace(NeedValue::Value(value.clone()));

                Ok(value)
            }
            None => Err(EvalError::Unbound(key.clone())),
        }
    }

    fn keys(&self) -> Box<dyn Iterator<Item = String>> {
        Box::new(
            self.storage
                .keys()
                .map(|s| s.clone())
                .collect::<Vec<String>>()
                .into_iter(),
        )
    }

    fn duplicate(&self) -> Box<dyn Environment> {
        Box::new(self.clone())
    }
}

impl Default for CallByNeed {
    fn default() -> Self {
        Self {
            storage: HashMap::new(),
        }
    }
}

impl BuildEnvironment for CallByNeed {}
