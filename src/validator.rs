// Core CBC Rust Library
// Copyright (C) 2018  Coordination Technology Ltd.
// Authors: pZ4 <pz4@protonmail.ch>,
//          Lederstrumpf,
//          h4sh3d <h4sh3d@truelevel.io>
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

//! ## Validators
//!
//! Validators produce and receive messages (`message::Trait`) from other validators in the
//! network. When a validator want to produce a message he needs to collect his justification
//! (`Justification`) and run an estimator (`Estimator`) to get a value. See [§ Estimator
//! Function](../justification/index.html#estimator-function) in § Justification.
//!
//! ## Consensus Rules
//!
//! These rules classify two types of faults: the *invalid message* fault, and the *equivocation* fault.
//!
//!  1. The proposed value must be in the set of consensus values returned by the application of
//!     the estimator function on the justification.
//!  1. The validator cannot make two messages with
//!     *  two different values, or
//!     *  two different justifications,
//!
//! such that **_either message is not later than the other_**.
//!
//! ### Violation of Consensus Rules
//!
//!  1. **Invalid Message Faults:** The violation of the first rule results in the message being
//!     invalid, and can be detected by everyone who receives the message. The receiver runs the
//!     estimator function on the justification of the message, and checks whether the proposed
//!     value is in the set of values returned by the estimator. All messages which do not violate
//!     this rule are valid messages.
//!  1. **Equivocation Faults:** The violation of the second rule cannot be detected by anyone who
//!     receives only one of the two messages violating this rule. This violation is a type of
//!     Byzantine failure which we call equivocation. We refer to the violation of this rule as
//!     faults.
//!
//! When a node (`validator::Trait`) equivocates, it is basically executing multiple separate
//! instances of the protocol, and may attempt to show messages from a single instance of these
//! executions to separate peers in the network. To clarify what separate instances of the protocol
//! are: consider a validator who violates consensus *rule 2* by generating messages **A** and
//! **B** that break the rule. The validator then starts maintaining two histories of protocol
//! execution, one in which only message **A** is generated, and the other in which only message
//! **B** is generated. In each single version of protocol execution, the validator has not
//! equivocated.
//!
//! Source: [Casper CBC, Simplified!](https://medium.com/@aditya.asgaonkar/casper-cbc-simplified-2370922f9aa6),
//! by Aditya Asgaonkar.

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::{Arc, LockResult, PoisonError, RwLock, RwLockReadGuard, RwLockWriteGuard};

use crate::justification::LatestMsgs;
use crate::message;
use crate::util::weight::{WeightUnit, Zero};

/// All casper actors that send messages, aka validators, have to implement the validator trait
pub trait Trait: Hash + Clone + Ord + Eq + Send + Sync + Debug + serde::Serialize {}

// Default implementations

impl Trait for u8 {}
impl Trait for u32 {}
impl Trait for u64 {}
impl Trait for i8 {}
impl Trait for i32 {}
impl Trait for i64 {}

/// Inner state of a validator. Validator's state implement `message::Trait` allowing validators to produce
/// messages based on their latest view of the network.
#[derive(Debug, Clone)]
pub struct State<M: message::Trait, U: WeightUnit> {
    /// current state total fault weight
    pub(crate) state_fault_weight: U,
    /// fault tolerance threshold
    pub(crate) thr: U,
    /// current validator set, mapped to their respective weights
    pub(crate) validators_weights: Weights<M::Sender, U>,
    /// this validator's latest message
    pub(crate) own_latest_msg: Option<M>,
    pub(crate) latest_msgs: LatestMsgs<M>,
    pub(crate) equivocators: HashSet<M::Sender>,
}

/// Error returned from the [`insert`], [`validators`] and [`weight`] function
/// on a [`Weights`]
///
/// [`insert`]: struct.Weights.html#method.insert
/// [`validators`]: struct.Weights.html#method.validators
/// [`weight`]: struct.Weights.html#method.weight
/// [`Weights`]: struct.Weights.html
pub enum Error<'rwlock, T> {
    WriteLockError(PoisonError<RwLockWriteGuard<'rwlock, T>>),
    ReadLockError(PoisonError<RwLockReadGuard<'rwlock, T>>),
    NotFound,
}

impl<'rwlock, T> std::error::Error for Error<'rwlock, T> {}

impl<'rwlock, T> std::fmt::Display for Error<'rwlock, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::NotFound => writeln!(f, "Validator weight not found"),
            Error::WriteLockError(p_err) => std::fmt::Display::fmt(p_err, f),
            Error::ReadLockError(p_err) => std::fmt::Display::fmt(p_err, f),
        }
    }
}

impl<'rwlock, T> std::fmt::Debug for Error<'rwlock, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::NotFound => writeln!(f, "Validator weight not found"),
            Error::WriteLockError(p_err) => std::fmt::Display::fmt(p_err, f),
            Error::ReadLockError(p_err) => std::fmt::Display::fmt(p_err, f),
        }
    }
}

impl<M: message::Trait, U: WeightUnit> State<M, U> {
    pub fn new(
        validators_weights: Weights<M::Sender, U>,
        state_fault_weight: U,
        own_latest_msg: Option<M>,
        latest_msgs: LatestMsgs<M>,
        thr: U,
        equivocators: HashSet<M::Sender>,
    ) -> Self {
        State {
            validators_weights,
            equivocators,
            state_fault_weight,
            thr,
            own_latest_msg,
            latest_msgs,
        }
    }

    pub fn from_state(
        validator_state: Self,
        validators_weights: Option<Weights<M::Sender, U>>,
        state_fault_weight: Option<U>,
        own_latest_msg: Option<M>,
        latest_msgs: Option<LatestMsgs<M>>,
        thr: Option<U>,
        equivocators: Option<HashSet<M::Sender>>,
    ) -> Self {
        State {
            validators_weights: validators_weights.unwrap_or(validator_state.validators_weights),
            state_fault_weight: state_fault_weight.unwrap_or(validator_state.state_fault_weight),
            own_latest_msg: own_latest_msg.or(validator_state.own_latest_msg),
            latest_msgs: latest_msgs.unwrap_or(validator_state.latest_msgs),
            thr: thr.unwrap_or(validator_state.thr),
            equivocators: equivocators.unwrap_or(validator_state.equivocators),
        }
    }

    pub fn equivocators(&self) -> &HashSet<M::Sender> {
        &self.equivocators
    }

    pub fn validators_weights(&self) -> &Weights<M::Sender, U> {
        &self.validators_weights
    }

    pub fn own_latest_msg(&self) -> &Option<M> {
        &self.own_latest_msg
    }

    pub fn latests_msgs(&self) -> &LatestMsgs<M> {
        &self.latest_msgs
    }

    pub fn latests_msgs_as_mut(&mut self) -> &mut LatestMsgs<M> {
        &mut self.latest_msgs
    }

    pub fn fault_weight(&self) -> U {
        self.state_fault_weight
    }

    /// get msgs and fault weight overhead and equivocators overhead sorted
    /// by fault weight overhead against the current validator_state
    pub fn sort_by_faultweight<'z>(&self, msgs: &HashSet<&'z M>) -> Vec<&'z M> {
        let mut msgs_sorted_by_faultw: Vec<_> = msgs
            .iter()
            .filter_map(|&msg| {
                // equivocations in relation to state
                let sender = msg.sender();
                if !self.equivocators.contains(sender) && self.latest_msgs.equivocate(msg) {
                    self.validators_weights
                        .weight(sender)
                        .map(|w| (msg, w))
                        .ok()
                } else {
                    Some((msg, <U as Zero<U>>::ZERO))
                }
            })
            .collect();

        msgs_sorted_by_faultw.sort_unstable_by(|(m0, w0), (m1, w1)| {
            w0.partial_cmp(w1)
                .unwrap_or_else(|| m0.getid().cmp(&m1.getid())) // tie breaker
        });

        // return a Vec<message::Trait>
        msgs_sorted_by_faultw
            .iter()
            .map(|(m, _)| m)
            .cloned()
            .collect()
    }
}

// Note: RwLock locks only before writing, while Mutex locks to both read and write
#[derive(Clone, Debug)]
pub struct Weights<V: self::Trait, U: WeightUnit>(Arc<RwLock<HashMap<V, U>>>);

impl<V: self::Trait, U: WeightUnit> Weights<V, U> {
    /// Creates a new weight set from a HashMap of validators to unit.
    pub fn new(weights: HashMap<V, U>) -> Self {
        Weights(Arc::new(RwLock::new(weights)))
    }

    /// Same as RwLock read function. Locks the Rwlock with read access.
    fn read(&self) -> LockResult<RwLockReadGuard<HashMap<V, U>>> {
        self.0.read()
    }

    /// Same as RwLock write function. Locks the RwLock with write access.
    fn write(&self) -> LockResult<RwLockWriteGuard<HashMap<V, U>>> {
        self.0.write()
    }

    /// Returns success of insertion. Failure happens if we cannot acquire the
    /// lock to write data.
    pub fn insert(&mut self, k: V, v: U) -> Result<bool, Error<HashMap<V, U>>> {
        self.write().map_err(Error::WriteLockError).map(|mut h| {
            h.insert(k, v);
            true
        })
    }

    /// Picks validators with positive weights striclty greather than zero.
    /// Failure happens if we cannot acquire the lock to read data
    pub fn validators(&self) -> Result<HashSet<V>, Error<HashMap<V, U>>> {
        self.read()
            .map_err(Error::ReadLockError)
            .map(|validators_weight| {
                validators_weight
                    .iter()
                    .filter_map(|(validator, &weight)| {
                        if weight > <U as Zero<U>>::ZERO {
                            Some(validator.clone())
                        } else {
                            None
                        }
                    })
                    .collect()
            })
    }

    /// Gets the weight of the validator. Returns an error in case there is a
    /// reading error or the validator does not exist.
    pub fn weight(&self, validator: &V) -> Result<U, Error<HashMap<V, U>>> {
        self.read()
            .map_err(Error::ReadLockError)
            .and_then(|weights| {
                weights
                    .get(validator)
                    .map(Clone::clone)
                    .ok_or(Error::NotFound)
            })
    }

    /// Returns the total weight of all the given validators.
    pub fn sum_weight_validators(&self, validators: &HashSet<V>) -> U {
        validators
            .iter()
            .fold(<U as Zero<U>>::ZERO, |acc, validator| {
                acc + self.weight(validator).unwrap_or(U::NAN)
            })
    }

    /// Returns the total weight of all the validators in the weights.
    pub fn sum_all_weights(&self) -> U {
        if let Ok(validators) = self.validators() {
            self.sum_weight_validators(&validators)
        } else {
            U::NAN
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::validator::Weights;

    #[test]
    fn include_positive_weight() {
        let weights = Weights::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        assert_eq!(
            Weights::validators(&weights).unwrap(),
            [0, 1, 2].iter().cloned().collect(),
            "should include validators with valid, positive weight"
        );
    }

    #[test]
    fn exclude_zero_weighted_validators() {
        let weights = Weights::new([(0, 0.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        assert_eq!(
            Weights::validators(&weights).unwrap(),
            [1, 2].iter().cloned().collect(),
            "should exclude validators with 0 weight"
        );
    }

    #[test]
    fn exclude_negative_weights() {
        let weights = Weights::new([(0, 1.0), (1, -1.0), (2, 1.0)].iter().cloned().collect());
        assert_eq!(
            Weights::validators(&weights).unwrap(),
            [0, 2].iter().cloned().collect(),
            "should exclude validators with negative weight"
        );
    }

    #[test]
    fn exclude_nan_weights() {
        let weights = Weights::new(
            [(0, ::std::f64::NAN), (1, 1.0), (2, 1.0)]
                .iter()
                .cloned()
                .collect(),
        );
        assert_eq!(
            Weights::validators(&weights).unwrap(),
            [1, 2].iter().cloned().collect(),
            "should exclude validators with NAN weight"
        );
    }

    #[test]
    fn include_infinity_weighted_validators() {
        let weights = Weights::new(
            [(0, ::std::f64::INFINITY), (1, 1.0), (2, 1.0)]
                .iter()
                .cloned()
                .collect(),
        );
        assert_eq!(
            Weights::validators(&weights).unwrap(),
            [0, 1, 2].iter().cloned().collect(),
            "should include validators with INFINITY weight"
        );
    }
}
