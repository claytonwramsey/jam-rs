//! A module for environments and binding rules. Contains implementations for
//! call-by-need, call-by-name, and call-by-value, as well as the traits
//! required to implement a custom binding scheme.

use std::{
    borrow::Borrow,
    cell::RefCell,
    collections::HashMap,
    fmt::{self, Debug},
    rc::{Rc, Weak},
};

use crate::{
    ast::Ast,
    evaluate::{evaluate_help, EvalError, EvalResult},
    value::{EitherValue, Value},
};

pub trait BuildEnvironment {
    /// Construct a new environment.
    fn build() -> Rc<dyn Environment>;
}

/// An environment is a structure which can be used to store and retrieve
/// values. Environments must be able to be cloned and compared for equality to
/// assist in the creation of maps. The default value of an environment will
/// always be an "empty" environment with no bindings.
pub trait Environment: Debug {
    /// Get the set of keys for this environment.
    fn keys(&self) -> Box<dyn Iterator<Item = String>>;

    /// Create a new environment with a new set of bindings corresponding to
    /// the items of the given iterator. The context is the environment in 
    /// which the new bindings must be made.
    fn with(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Ast)>,
        context: Rc<dyn Environment>,
    ) -> Result<Rc<dyn Environment>, EvalError>;

    /// Create a new environment, supporting recursive evaluation of each
    /// binding.
    fn with_recursive(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Ast)>,
    ) -> Result<Rc<dyn Environment>, EvalError>;

    /// Get the key from an environment. Returns an unbound error if it is
    /// unable to get the key. Although the pointer to `self` is mutable, the
    /// environment may not remove any bindings - this is for call-by-need.
    fn get(&self, key: &str) -> EvalResult;
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

        for k2 in other.keys() {
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

/// An environment for call-by-value.
pub struct CallByValue {
    /// The stored key-value pairs.
    storage: HashMap<String, RefCell<Option<EitherValue>>>,
    /// A weak pointer to ourself. We may assume it is always initialized
    /// correctly.
    self_rc: Weak<CallByValue>,
}

impl CallByValue {
    /// Create a copy of the internal storage, promiting any weak references
    /// along the way.
    fn clone_storage(&self) -> HashMap<String, RefCell<Option<EitherValue>>> {
        self.storage
            .iter()
            .map(|(key, value)| {
                (
                    key.clone(),
                    RefCell::new(value.borrow().as_ref().map(|either| either.as_strong())),
                )
            })
            .collect()
    }

    fn with_storage(storage: HashMap<String, RefCell<Option<EitherValue>>>) -> Rc<CallByValue> {
        Rc::new_cyclic(|self_rc| CallByValue {
            storage,
            self_rc: self_rc.clone(),
        })
    }
}

impl Environment for CallByValue {
    fn keys(&self) -> Box<dyn Iterator<Item = String>> {
        Box::new(
            self.storage
                .keys()
                .cloned()
                .collect::<Vec<String>>()
                .into_iter(),
        )
    }

    fn get(&self, key: &str) -> EvalResult {
        Ok(self
            .storage
            .get(key)
            // no key found
            .ok_or_else(|| EvalError::Unbound(key.into()))?
            .borrow()
            .clone()
            // key found, but not evaluated
            .ok_or_else(|| EvalError::ForwardReference(key.into()))?
            .into())
    }

    fn with(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Ast)>,
        context: Rc<dyn Environment>,
    ) -> Result<Rc<dyn Environment>, EvalError> {
        let mut new_storage = self.clone_storage();
        for (key, body) in bindings {
            let value = evaluate_help(body, context.clone())?;

            new_storage.insert(key.clone(), RefCell::new(Some(value.into())));
        }
        Ok(CallByValue::with_storage(new_storage))
    }

    fn with_recursive(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Ast)>,
    ) -> Result<Rc<dyn Environment>, EvalError> {
        let mut new_storage = self.clone_storage();
        let collected_bindings: Vec<(&String, &Ast)> = bindings.collect();
        for (key, _) in collected_bindings.iter() {
            // start by storing a dummy value for this key before we lose
            // mutability
            new_storage.insert(key.to_string(), RefCell::new(None));
        }
        let new_env = CallByValue::with_storage(new_storage);
        for (key, body) in collected_bindings {
            println!("binding {key} to {body}");
            let either: EitherValue = evaluate_help(body, new_env.clone())?.into();
            // now evaluate the body using our new environment
            new_env.storage[key].replace(Some(either.demote_in(new_env.clone())));
            println!("bound {key} to {body}");
        }
        Ok(new_env)
    }
}

impl BuildEnvironment for CallByValue {
    fn build() -> Rc<dyn Environment> {
        Rc::new_cyclic(|self_rc| CallByValue {
            storage: HashMap::new(),
            self_rc: self_rc.clone(),
        })
    }
}

impl Debug for CallByValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CallByValue {{ ")?;
        for (key, value) in self.storage.iter() {
            write!(
                f,
                "{key:?}: {:?}, ",
                value
            )?;
        }
        write!(f, "}}")
    }
}

/* Call-by-name */

#[derive(Clone, Debug)]
/// A call-by-name environment.
pub struct CallByName {
    /// map from variables to the ASTs they represent
    /// wrapped in a cell to allow overwriting
    /// If the outermost option is `None`, then the cell has been initialized
    /// but not set.
    /// environments are wrapped in an `Option`. if the option is `None`, then
    /// we will use ourselves as an evaluator.
    storage: HashMap<String, RefCell<Option<(Option<Rc<dyn Environment>>, Ast)>>>,
    /// A weak RC pointing to ourself. The wrapping cell and option are used
    /// for construction, but can be assumed to be properly initialized with
    /// `Some` by the time of operation.
    self_rc: Weak<CallByName>,
}

impl Environment for CallByName {
    fn get(&self, key: &str) -> EvalResult {
        todo!()
    }

    fn keys(&self) -> Box<dyn Iterator<Item = String>> {
        todo!()
    }

    fn with(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Ast)>,
        context: Rc<dyn Environment>,
    ) -> Result<Rc<dyn Environment>, EvalError> {
        todo!()
    }

    fn with_recursive(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Ast)>,
    ) -> Result<Rc<dyn Environment>, EvalError> {
        todo!()
    }
}

impl BuildEnvironment for CallByName {
    fn build() -> Rc<dyn Environment> {
        Rc::new_cyclic(|self_rc| CallByName {
            storage: HashMap::new(),
            self_rc: self_rc.clone(),
        })
    }
}

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

#[derive(Debug, Clone, Default)]
/// A call-by-need environment.
pub struct CallByNeed {
    storage: HashMap<String, Option<RefCell<NeedValue>>>,
    self_rc: Weak<CallByNeed>,
}

impl Environment for CallByNeed {
    fn keys(&self) -> Box<dyn Iterator<Item = String>> {
        todo!()
    }

    fn with(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Ast)>,
        context: Rc<dyn Environment>,
    ) -> Result<Rc<dyn Environment>, EvalError> {
        todo!()
    }

    fn with_recursive(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Ast)>,
    ) -> Result<Rc<dyn Environment>, EvalError> {
        todo!()
    }

    fn get(&self, key: &str) -> EvalResult {
        todo!()
    }
}

impl BuildEnvironment for CallByNeed {
    fn build() -> Rc<dyn Environment> {
        Rc::new_cyclic(|self_rc| CallByNeed {
            storage: HashMap::new(),
            self_rc: self_rc.clone(),
        })
    }
}
