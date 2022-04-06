use std::{collections::HashMap, fmt::Debug};

use crate::{ast::Ast, evaluate::{EvalResult, EvalError, evaluate_help}, value::Value};

/// An environment is a structure which can be used to store and retrieve 
/// values. Environments must be able to be cloned and compared for equality to 
/// assist in the creation of maps. The default value of an environment will 
/// always be an "empty" environment with no bindings.
pub trait Environment: Clone + Eq + Default + Debug {
    /// Store a key in the environment. The context is the 
    fn store(
        &mut self, 
        context: &mut Self, 
        key: &String, 
        body: &Ast,
    ) -> Result<(), EvalError<Self>>;
    /// Get the key from an environment. Returns an unbound error if it is 
    /// unable to get the key. Although the pointer to `self` is mutable, the 
    /// environment may not remove any bindings - this is for call-by-need.
    fn get(&mut self, key: &String) -> EvalResult<Self>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// An environment for call-by-value.
pub struct ValueEnvironment {
    /// The stored key-value pairs.
    storage: HashMap<String, Value<Self>>,
}

impl Environment for ValueEnvironment {
    /// Store a value. Will eagerly evaluate the body to get the resulting 
    /// value.
    fn store(
        &mut self, 
        context: &mut Self, 
        key: &String, 
        body: &Ast,
    ) -> Result<(), EvalError<Self>> {
        self.storage.insert(
            key.clone(),
            evaluate_help::<ValueEnvironment>(&body, context)?,
        );

        Ok(())
    }

    /// Get a key 
    fn get(&mut self, key: &String) -> EvalResult<Self> {
        Ok(self
            .storage
            .get(key)
            .ok_or(EvalError::Unbound(key.clone()))?
            .clone()
        )
    }
}

impl Default for ValueEnvironment {
    fn default() -> ValueEnvironment {
        ValueEnvironment { 
            storage: HashMap::new(),
        }
    }
}