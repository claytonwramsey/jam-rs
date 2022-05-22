//! A module for environments and binding rules. Contains implementations for
//! call-by-need, call-by-name, and call-by-value, as well as the traits
//! required to implement a custom binding scheme.

use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::{self, Debug},
    rc::{Rc, Weak},
};

use crate::{
    ast::Ast,
    evaluate::{evaluate_help, EvalError, EvalResult},
    value::{demote_in, strengthen, EitherValue, Value},
};

/// A simple builder trait for creating environments.
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
        bindings: &mut dyn Iterator<Item = (&String, &Rc<Ast>)>,
        context: Rc<dyn Environment>,
    ) -> Result<Rc<dyn Environment>, EvalError>;

    /// Create a new environment, supporting recursive evaluation of each
    /// binding.
    fn with_recursive(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Rc<Ast>)>,
    ) -> Result<Rc<dyn Environment>, EvalError>;

    /// Get the key from an environment. Returns an unbound error if it is
    /// unable to get the key. Although the pointer to `self` is mutable, the
    /// environment may not remove any bindings - this is for call-by-need.
    fn get(&self, key: &str) -> Result<Value, EvalError>;
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
    storage: HashMap<String, RefCell<Option<Rc<EitherValue>>>>,
}

impl CallByValue {
    /// Create a copy of the internal storage, promiting any weak references
    /// along the way.
    fn clone_storage(&self) -> HashMap<String, RefCell<Option<Rc<EitherValue>>>> {
        self.storage
            .iter()
            .map(|(key, value)| {
                (
                    key.clone(),
                    RefCell::new(value.borrow().as_ref().map(strengthen)),
                )
            })
            .collect()
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
            .as_ref()
            // key found, but not evaluated
            .ok_or_else(|| EvalError::ForwardReference(key.into()))?
            .into())
    }

    fn with(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Rc<Ast>)>,
        context: Rc<dyn Environment>,
    ) -> Result<Rc<dyn Environment>, EvalError> {
        let mut new_storage = self.clone_storage();
        for (key, body) in bindings {
            let value = evaluate_help(body, context.clone())?;

            new_storage.insert(key.clone(), RefCell::new(Some(Rc::new(value.into()))));
        }
        Ok(Rc::new(CallByValue {
            storage: new_storage,
        }))
    }

    fn with_recursive(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Rc<Ast>)>,
    ) -> Result<Rc<dyn Environment>, EvalError> {
        let mut new_storage = self.clone_storage();
        let collected_bindings: Vec<(&String, &Rc<Ast>)> = bindings.collect();
        for (key, _) in collected_bindings.iter() {
            // start by storing a dummy value for this key before we lose
            // mutability
            new_storage.insert(key.to_string(), RefCell::new(None));
        }
        let new_env = Rc::new(CallByValue {
            storage: new_storage,
        });
        for (key, body) in collected_bindings {
            let either = Rc::new(evaluate_help(body, new_env.clone())?.into());
            // now evaluate the body using our new environment
            new_env.storage[key].replace(Some(demote_in(&either, new_env.as_ref())));
        }
        Ok(new_env)
    }
}

impl BuildEnvironment for CallByValue {
    fn build() -> Rc<dyn Environment> {
        Rc::new(CallByValue {
            storage: HashMap::new(),
        })
    }
}

impl Debug for CallByValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CallByValue {{ ")?;
        for (key, value) in self.storage.iter() {
            write!(f, "{key:?}: {:?}, ", value)?;
        }
        write!(f, "}}")
    }
}

/* Call-by-name. */

/// The type of a value in call-by-name. Environments are wrapped in an
/// `Option`. if the option is `None`, then we will use ourselves as an
/// evaluator.
type NameValue = (Option<Rc<dyn Environment>>, Rc<Ast>);

#[derive(Clone, Debug)]
/// A call-by-name environment.
pub struct CallByName {
    /// Map from variables to the ASTs they represent. The contents are wrapped
    /// wrapped in a cell to allow overwriting for recursion.
    /// If the outermost option is `None`, then the cell has been initialized
    /// but not set.
    storage: HashMap<String, RefCell<Option<NameValue>>>,
    /// A weak RC pointing to ourself. We can always safely upgrade this, since
    /// if we can access this, we must still exist.
    self_rc: Weak<CallByName>,
}

impl CallByName {
    fn clone_storage(&self) -> HashMap<String, RefCell<Option<NameValue>>> {
        self.storage
            .iter()
            .map(|(key, value)| (key.clone(), RefCell::new(value.borrow().clone())))
            .collect()
    }

    /// Construct a new `CallByName` with a given set of storage.
    fn with_storage(storage: HashMap<String, RefCell<Option<NameValue>>>) -> Rc<CallByName> {
        Rc::new_cyclic(|self_rc| CallByName {
            storage,
            self_rc: self_rc.clone(),
        })
    }
}

impl Environment for CallByName {
    fn get(&self, key: &str) -> EvalResult {
        let cell = self
            .storage
            .get(key)
            // unable to find match for this key
            .ok_or_else(|| EvalError::Unbound(key.into()))?;

        let cell_ref = (*cell).borrow();

        let (opt_env, body) = cell_ref
            .as_ref()
            .ok_or_else(|| EvalError::ForwardReference(key.into()))?;

        let env = match opt_env {
            Some(e) => e.clone(),
            None => self.self_rc.upgrade().unwrap(),
        };

        evaluate_help(body, env)
    }

    fn keys(&self) -> Box<dyn Iterator<Item = String>> {
        Box::new(
            self.storage
                .keys()
                .cloned()
                .collect::<Vec<String>>()
                .into_iter(),
        )
    }

    fn with(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Rc<Ast>)>,
        context: Rc<dyn Environment>,
    ) -> Result<Rc<dyn Environment>, EvalError> {
        let mut new_storage = self.clone_storage();
        for (key, body) in bindings {
            new_storage.insert(
                key.clone(),
                RefCell::new(Some((Some(context.clone()), body.clone()))),
            );
        }
        Ok(CallByName::with_storage(new_storage))
    }

    fn with_recursive(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Rc<Ast>)>,
    ) -> Result<Rc<dyn Environment>, EvalError> {
        // collect so we can iterate twice
        let mut new_storage = self.clone_storage();
        let collected_bindings: Vec<(&String, &Rc<Ast>)> = bindings.collect();

        for (key, _) in collected_bindings.iter() {
            new_storage.insert(key.to_string(), RefCell::new(None));
        }

        let new_env = CallByName::with_storage(new_storage);

        for (key, body) in collected_bindings {
            new_env.storage[key].replace(Some((None, body.clone())));
        }

        Ok(new_env)
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

#[derive(Clone, Debug, PartialEq, Eq)]
/// The internal values of bindings in a call-by-need environment.
enum NeedValue {
    /// The value has not yet been evaluated. Will be `None` if it must be
    /// evaluated with the environment it is stored in.
    Ast(Option<Rc<dyn Environment>>, Rc<Ast>),
    /// The value has been evaluated.
    Value(Value),
}

#[derive(Debug, Clone, Default)]
/// A call-by-need environment.
pub struct CallByNeed {
    /// The stored values.
    storage: HashMap<String, RefCell<Option<NeedValue>>>,
    /// A reference to ourselves, for use in recursion.
    self_rc: Weak<CallByNeed>,
}

impl CallByNeed {
    fn clone_storage(&self) -> HashMap<String, RefCell<Option<NeedValue>>> {
        self.storage
            .iter()
            .map(|(key, value)| (key.clone(), RefCell::new(value.borrow().clone())))
            .collect()
    }

    /// Construct a new `CallByName` with a given set of storage.
    fn with_storage(storage: HashMap<String, RefCell<Option<NeedValue>>>) -> Rc<CallByNeed> {
        Rc::new_cyclic(|self_rc| CallByNeed {
            storage,
            self_rc: self_rc.clone(),
        })
    }
}

impl Environment for CallByNeed {
    fn keys(&self) -> Box<dyn Iterator<Item = String>> {
        Box::new(
            self.storage
                .keys()
                .cloned()
                .collect::<Vec<String>>()
                .into_iter(),
        )
    }

    fn with(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Rc<Ast>)>,
        context: Rc<dyn Environment>,
    ) -> Result<Rc<dyn Environment>, EvalError> {
        let mut new_storage = self.clone_storage();
        for (key, body) in bindings {
            new_storage.insert(
                key.clone(),
                RefCell::new(Some(NeedValue::Ast(Some(context.clone()), body.clone()))),
            );
        }
        Ok(CallByNeed::with_storage(new_storage))
    }

    fn with_recursive(
        &self,
        bindings: &mut dyn Iterator<Item = (&String, &Rc<Ast>)>,
    ) -> Result<Rc<dyn Environment>, EvalError> {
        // collect so we can iterate twice
        let mut new_storage = self.clone_storage();
        let collected_bindings: Vec<(&String, &Rc<Ast>)> = bindings.collect();

        for (key, _) in collected_bindings.iter() {
            new_storage.insert(key.to_string(), RefCell::new(None));
        }

        let new_env = CallByNeed::with_storage(new_storage);

        for (key, body) in collected_bindings {
            new_env.storage[key].replace(Some(NeedValue::Ast(None, body.clone())));
        }

        Ok(new_env)
    }

    fn get(&self, key: &str) -> EvalResult {
        let cell = self
            .storage
            .get(key)
            // unable to find match for this key
            .ok_or_else(|| EvalError::Unbound(key.into()))?;

        let value = match &*cell.borrow() {
            Some(NeedValue::Ast(env, ast)) => evaluate_help(
                ast,
                env.clone()
                    .unwrap_or_else(|| self.self_rc.upgrade().unwrap()),
            )?,
            Some(NeedValue::Value(val)) => return Ok(val.clone()),
            None => return Err(EvalError::ForwardReference(key.into())),
        };
        cell.replace(Some(NeedValue::Value(value.clone())));

        Ok(value)
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
