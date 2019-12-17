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
//! Validators produce and receive messages (`message::Message`) from other validators in the
//! network. When a validator want to produce a message he needs to collect his justification
//! (`Justification`) and run an estimator (`Estimator`) to get a value. See [§ Estimator
//! Function](../justification/index.html#estimator-function) in § Justification.
//!
//! ## Consensus Rules
//!
//! These rules classify two types of faults: the *invalid message* fault, and the *equivocation*
//! fault.
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
//! When a node (`validator::ValidatorName`) equivocates, it is basically executing multiple
//! separate instances of the protocol, and may attempt to show messages from a single instance of
//! these executions to separate peers in the network. To clarify what separate instances of the
//! protocol are: consider a validator who violates consensus *rule 2* by generating messages **A**
//! and **B** that break the rule. The validator then starts maintaining two histories of protocol
//! execution, one in which only message **A** is generated, and the other in which only message
//! **B** is generated. In each single version of protocol execution, the validator has not
//! equivocated.
//!
//! Source: [Casper CBC, Simplified!](
//! https://medium.com/@aditya.asgaonkar/casper-cbc-simplified-2370922f9aa6),
//! by Aditya Asgaonkar.

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::{Arc, LockResult, PoisonError, RwLock, RwLockReadGuard, RwLockWriteGuard};

use crate::estimator::Estimator;
use crate::justification::LatestMsgs;
use crate::message::Message;
use crate::util::id::Id;
use crate::util::weight::{WeightUnit, Zero};

/// All casper actors that send messages, aka validators, have to implement the validator name
/// trait
pub trait ValidatorName: Hash + Clone + Ord + Eq + Send + Sync + Debug + serde::Serialize {}

// Default implementations

impl ValidatorName for u8 {}
impl ValidatorName for u32 {}
impl ValidatorName for u64 {}
impl ValidatorName for i8 {}
impl ValidatorName for i32 {}
impl ValidatorName for i64 {}

/// Inner state of a validator. This represents the validator's view
/// of the network.
#[derive(Debug, Clone)]
pub struct State<E, U>
where
    E: Estimator,
    U: WeightUnit,
{
    /// current state total fault weight
    pub(crate) state_fault_weight: U,
    /// fault tolerance threshold
    pub(crate) thr: U,
    /// current validator set, mapped to their respective weights
    pub(crate) validators_weights: Weights<E::ValidatorName, U>,
    pub(crate) latest_msgs: LatestMsgs<E>,
    pub(crate) equivocators: HashSet<E::ValidatorName>,
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

impl<E, U> State<E, U>
where
    E: Estimator,
    U: WeightUnit,
{
    pub fn new(
        validators_weights: Weights<E::ValidatorName, U>,
        state_fault_weight: U,
        latest_msgs: LatestMsgs<E>,
        thr: U,
        equivocators: HashSet<E::ValidatorName>,
    ) -> Self {
        State {
            validators_weights,
            equivocators,
            state_fault_weight,
            thr,
            latest_msgs,
        }
    }

    pub fn new_with_default_state(
        default_state: Self,
        validators_weights: Option<Weights<E::ValidatorName, U>>,
        state_fault_weight: Option<U>,
        latest_msgs: Option<LatestMsgs<E>>,
        thr: Option<U>,
        equivocators: Option<HashSet<E::ValidatorName>>,
    ) -> Self {
        State {
            validators_weights: validators_weights.unwrap_or(default_state.validators_weights),
            state_fault_weight: state_fault_weight.unwrap_or(default_state.state_fault_weight),
            latest_msgs: latest_msgs.unwrap_or(default_state.latest_msgs),
            thr: thr.unwrap_or(default_state.thr),
            equivocators: equivocators.unwrap_or(default_state.equivocators),
        }
    }

    /// Adds messages to the state's latests_msgs. Returns true if
    /// all messages added are valid latest messages.
    pub fn update(&mut self, messages: &[&Message<E>]) -> bool {
        messages.iter().fold(true, |acc, message| {
            let sender = message.sender();
            let weight = self
                .validators_weights
                .weight(sender)
                .unwrap_or(U::INFINITY);

            let a = self.latest_msgs.update(message);

            if self.latest_msgs.equivocate(message)
                && weight + self.state_fault_weight <= self.thr
                && self.equivocators.insert(sender.clone())
            {
                self.state_fault_weight += weight;
            }

            acc && a
        })
    }

    pub fn equivocators(&self) -> &HashSet<E::ValidatorName> {
        &self.equivocators
    }

    pub fn validators_weights(&self) -> &Weights<E::ValidatorName, U> {
        &self.validators_weights
    }

    pub fn latests_msgs(&self) -> &LatestMsgs<E> {
        &self.latest_msgs
    }

    pub fn latests_msgs_as_mut(&mut self) -> &mut LatestMsgs<E> {
        &mut self.latest_msgs
    }

    pub fn fault_weight(&self) -> U {
        self.state_fault_weight
    }

    /// get msgs and fault weight overhead and equivocators overhead sorted
    /// by fault weight overhead against the current validator_state
    pub fn sort_by_faultweight<'z>(&self, msgs: &HashSet<&'z Message<E>>) -> Vec<&'z Message<E>> {
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

        msgs_sorted_by_faultw
            .iter()
            .map(|(m, _)| m)
            .cloned()
            .collect()
    }
}

// Note: RwLock locks only before writing, while Mutex locks to both read and write
#[derive(Clone, Debug)]
pub struct Weights<V: self::ValidatorName, U: WeightUnit>(Arc<RwLock<HashMap<V, U>>>);

impl<V: self::ValidatorName, U: WeightUnit> Weights<V, U> {
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
        self.write()
            .map_err(Error::WriteLockError)
            .map(|mut hash_map| {
                hash_map.insert(k, v);
                true
            })
    }

    /// Picks validators with positive weights striclty greather than zero.
    /// Failure happens if we cannot acquire the lock to read data
    pub fn validators(&self) -> Result<HashSet<V>, Error<HashMap<V, U>>> {
        self.read().map_err(Error::ReadLockError).map(|hash_map| {
            hash_map
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
            .and_then(|hash_map| {
                hash_map
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
    use super::*;

    use crate::VoteCount;

    use std::iter::FromIterator;

    #[test]
    fn weights_validators_include_positive_weight() {
        let weights = Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect());
        assert_eq!(
            weights.validators().unwrap(),
            vec![0, 1, 2].into_iter().collect(),
            "should include validators with valid, positive weight"
        );
    }

    #[test]
    fn weights_validators_exclude_zero_weighted_validators() {
        let weights = Weights::new(vec![(0, 0.0), (1, 1.0), (2, 1.0)].into_iter().collect());
        assert_eq!(
            weights.validators().unwrap(),
            vec![1, 2].into_iter().collect(),
            "should exclude validators with 0 weight"
        );
    }

    #[test]
    fn weights_validators_exclude_negative_weights() {
        let weights = Weights::new(vec![(0, 1.0), (1, -1.0), (2, 1.0)].into_iter().collect());
        assert_eq!(
            weights.validators().unwrap(),
            vec![0, 2].into_iter().collect(),
            "should exclude validators with negative weight"
        );
    }

    #[test]
    fn weights_validators_exclude_nan_weights() {
        let weights = Weights::new(
            vec![(0, f32::NAN), (1, 1.0), (2, 1.0)]
                .into_iter()
                .collect(),
        );
        assert_eq!(
            weights.validators().unwrap(),
            vec![1, 2].into_iter().collect(),
            "should exclude validators with NAN weight"
        );
    }

    #[test]
    fn weights_validators_include_infinity_weighted_validators() {
        let weights = Weights::new(
            vec![(0, f32::INFINITY), (1, 1.0), (2, 1.0)]
                .into_iter()
                .collect(),
        );
        assert_eq!(
            weights.validators().unwrap(),
            vec![0, 1, 2].into_iter().collect(),
            "should include validators with INFINITY weight"
        );
    }

    #[test]
    fn weights_weight() {
        let weights = Weights::new(
            vec![(0, 1.0), (1, -1.0), (2, f32::INFINITY)]
                .into_iter()
                .collect(),
        );
        // Accessing the weights directly does not hide anything
        float_eq!(weights.weight(&0).unwrap(), 1.0);
        float_eq!(weights.weight(&1).unwrap(), -1.0);
        assert!(weights.weight(&2).unwrap().is_infinite());
    }

    #[test]
    fn weights_weight_not_found() {
        let weights = Weights::<u32, f32>::new(vec![].into_iter().collect());
        match weights.weight(&0) {
            Err(Error::NotFound) => (),
            _ => panic!("Expected Error::NotFound"),
        };
    }

    #[test]
    fn weights_sum_weight_validators() {
        let weights = Weights::new(
            vec![(0, 1.0), (1, -1.0), (2, 3.3), (3, f32::INFINITY)]
                .into_iter()
                .collect(),
        );
        assert!(weights
            .sum_weight_validators(&HashSet::from_iter(vec![0, 1, 3]))
            .is_infinite());
        float_eq!(
            weights.sum_weight_validators(&HashSet::from_iter(vec![0, 1])),
            0.0
        );
        float_eq!(
            weights.sum_weight_validators(&HashSet::from_iter(vec![0, 2])),
            4.3
        );
        assert!(weights
            .sum_weight_validators(&HashSet::from_iter(vec![4]))
            .is_nan());
    }

    #[test]
    fn weights_sum_all_weights() {
        let weights = Weights::new(vec![(0, 2.0), (1, -1.0), (2, 3.3)].into_iter().collect());
        // Does not account for negatively weigthed validators
        float_eq!(
            weights.sum_all_weights(),
            weights.sum_weight_validators(&HashSet::from_iter(vec![0, 2]))
        );
    }

    #[test]
    fn validator_state_update() {
        let mut validator_state = State::new(
            Weights::new(vec![(0, 1.0), (1, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            2.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_msg(0, false);
        let v1 = VoteCount::create_vote_msg(1, true);

        let all_valid = validator_state.update(&[&v0, &v1]);

        let hs0 = validator_state
            .latests_msgs()
            .get(&0)
            .expect("state should contain validator 0");
        let hs1 = validator_state
            .latests_msgs()
            .get(&1)
            .expect("state should contain validator 1");

        assert!(all_valid, "messages should not be all valid messages");
        assert_eq!(
            hs0.len(),
            1,
            "validator_state should have only 1 message for validator 0",
        );
        assert_eq!(
            hs1.len(),
            1,
            "validator_state should have only 1 message for validator 1",
        );
        assert!(hs0.contains(&v0), "validator_state should contain v0");
        assert!(hs1.contains(&v1), "validator_state should contain v1");
        float_eq!(
            validator_state.fault_weight(),
            0.0,
            "fault weight should be 0"
        );
        assert!(
            validator_state.equivocators().is_empty(),
            "no equivocators should exist",
        );
    }

    #[test]
    fn validator_state_update_equivocate_under_threshold() {
        let mut validator_state = State::new(
            Weights::new(vec![(0, 1.0), (1, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            2.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true);
        let v1 = VoteCount::create_vote_msg(1, true);

        let all_valid = validator_state.update(&[&v0, &v0_prime, &v1]);

        let hs0 = validator_state
            .latests_msgs()
            .get(&0)
            .expect("state should contain validator 0");
        let hs1 = validator_state
            .latests_msgs()
            .get(&1)
            .expect("state should contain validator 1");

        assert!(all_valid, "messages should not be all valid messages");
        assert_eq!(
            hs0.len(),
            2,
            "validator_state should have 2 messages for validator 0",
        );
        assert_eq!(
            hs1.len(),
            1,
            "validator_state should have only 1 message for validator 1",
        );
        assert!(hs0.contains(&v0), "validator_state should contain v0");
        assert!(
            hs0.contains(&v0_prime),
            "validator_state should contain v0_prime",
        );
        assert!(hs1.contains(&v1), "validator_state should contain v1");
        float_eq!(
            validator_state.fault_weight(),
            1.0,
            "fault weight should be 1"
        );
        assert!(
            validator_state.equivocators().contains(&0),
            "validator 0 should be in equivocators",
        );
    }

    #[test]
    fn validator_state_update_equivocate_at_threshold() {
        let mut validator_state = State::new(
            Weights::new(vec![(0, 1.0), (1, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true);
        let v1 = VoteCount::create_vote_msg(1, true);

        let all_valid = validator_state.update(&[&v0, &v0_prime, &v1]);

        let hs0 = validator_state
            .latests_msgs()
            .get(&0)
            .expect("state should contain validator 0");
        let hs1 = validator_state
            .latests_msgs()
            .get(&1)
            .expect("state should contain validator 1");

        assert!(all_valid, "messages should not be all valid messages");
        assert_eq!(
            hs0.len(),
            2,
            "validator_state should have 2 messages for validator 0",
        );
        assert_eq!(
            hs1.len(),
            1,
            "validator_state should have only 1 message for validator 1",
        );
        assert!(hs0.contains(&v0), "validator_state should contain v0");
        assert!(
            hs0.contains(&v0_prime),
            "validator_state should contain v0_prime",
        );
        assert!(hs1.contains(&v1), "validator_state should contain v1");
        float_eq!(
            validator_state.fault_weight(),
            0.0,
            "fault weight should be 0"
        );
        assert!(
            validator_state.equivocators().is_empty(),
            "validator 0 should not be in equivocators"
        );
    }
}
