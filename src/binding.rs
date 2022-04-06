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

/* Call-by-value */

#[derive(Clone, Debug, PartialEq, Eq)]
/// An environment for call-by-value.
pub struct CallByValue {
    /// The stored key-value pairs.
    storage: HashMap<String, Value<Self>>,
}

impl Environment for CallByValue {
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
            evaluate_help::<CallByValue>(&body, context)?,
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

impl Default for CallByValue {
    fn default() -> CallByValue {
        CallByValue { 
            storage: HashMap::new(),
        }
    }
}

/* Call-by-name */

#[derive(Clone, Debug, PartialEq, Eq)]
/// A call-by-name environment.
pub struct CallByName {
    /// map from variables to the ASTs they represent
    storage: HashMap<String, (CallByName, Ast)>,
}

impl Environment for CallByName {
    fn store(
        &mut self, 
        context: &mut Self, 
        key: &String, 
        body: &Ast,
    ) -> Result<(), EvalError<Self>> {
        self.storage.insert(key.clone(), (context.clone(), body.clone()));

        Ok(())
    }

    fn get(&mut self, key: &String) -> EvalResult<Self> {
        let (env, body) = self.storage
            .get_mut(key)
            .ok_or(EvalError::Unbound(key.clone()))?;
        evaluate_help(body, env)
    }
}

impl Default for CallByName {
    fn default() -> CallByName {
        CallByName { storage: HashMap::new() }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// The internal values of bindings in a call-by-need environment.
enum NeedValue {
    /// The value has not yet been evaluated.
    Ast(CallByNeed, Ast),
    /// The value has been evaluated.
    Value(Value<CallByNeed>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallByNeed {
    storage: HashMap<String, NeedValue>
}

impl Environment for CallByNeed {
    fn store(
        &mut self, 
        context: &mut Self, 
        key: &String, 
        body: &Ast,
    ) -> Result<(), EvalError<Self>> {
        self.storage.insert(key.clone(), NeedValue::Ast(
            context.clone(), 
            body.clone(),
        ));

        Ok(())
    }

    fn get(&mut self, key: &String) -> EvalResult<Self> {
        match self.storage.get_mut(key) {
            Some(NeedValue::Ast(env, ast)) => {
                let value = evaluate_help(&ast, env)?;
                self.storage.insert(
                    key.clone(), 
                    NeedValue::Value(value.clone())
                );
                Ok(value)
            }
            Some(NeedValue::Value(v)) => Ok(v.clone()),
            None => Err(EvalError::Unbound(key.clone())),
        }
    }
}

impl Default for CallByNeed {
    fn default() -> Self {
        Self { 
            storage: HashMap::new() 
        }
    }
}