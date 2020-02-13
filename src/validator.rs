// Core CBC Casper
// Copyright (C) 2018 - 2020  Coordination Technology Ltd.
// Authors: pZ4 <pz4@protonmail.ch>,
//          Lederstrumpf,
//          h4sh3d <h4sh3d@truelevel.io>
//          roflolilolmao <q@truelevel.ch>
//
// This file is part of Core CBC Casper.
//
// Core CBC Casper is free software: you can redistribute it and/or modify it under the terms
// of the GNU Affero General Public License as published by the Free Software Foundation, either
// version 3 of the License, or (at your option) any later version.
//
// Core CBC Casper is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
// PURPOSE. See the GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License along with the Core CBC
// Rust Library. If not, see <https://www.gnu.org/licenses/>.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::{Arc, LockResult, PoisonError, RwLock, RwLockReadGuard, RwLockWriteGuard};

use crate::estimator::Estimator;
use crate::justification::LatestMessages;
use crate::message::Message;
use crate::util::id::Id;
use crate::util::weight::{WeightUnit, Zero};

/// All casper actors that send messages, aka validators, have to implement the validator name
/// trait. This trait serves as an identifier for validators.
///
/// The basic types u8, u32, u64, i8, i32, and i64 implement ValidatorName trivially.
///
/// # Example
///
/// ```
/// use core_cbc_casper::validator::Weights;
/// use core_cbc_casper::validator::ValidatorName;
///
/// #[derive(Hash, Clone, PartialOrd, Ord, PartialEq, Eq, Debug, serde_derive::Serialize)]
/// struct StringName {
///     name: String,
/// }
///
/// // Implementing the ValidatorName trait for a string wrapper.
/// impl ValidatorName for StringName {};
///
/// let weights = Weights::new(
///     vec![(StringName { name: "John".to_string() }, 1.0)].into_iter().collect(),
/// );
///
/// // We can find the weight a validator in a Weights structure using its name.
/// assert_eq!(
///     weights.weight(&StringName { name: "John".to_string() }).unwrap(),
///     1.0,
/// );
/// ```
pub trait ValidatorName: Hash + Clone + Ord + Eq + Send + Sync + Debug + serde::Serialize {}

// Default implementations for simple types.
impl ValidatorName for u8 {}
impl ValidatorName for u32 {}
impl ValidatorName for u64 {}
impl ValidatorName for i8 {}
impl ValidatorName for i32 {}
impl ValidatorName for i64 {}

/// Inner state of a validator. This represents the validator's view of the network.
///
/// # Example
///
/// Using the [`VoteCount`] type message type for brevity's sake.
///
/// [`VoteCount`]: ../struct.VoteCount.html
///
/// ```
/// use core_cbc_casper::justification::LatestMessages;
/// use core_cbc_casper::validator::{State, Weights};
/// use core_cbc_casper::VoteCount;
///
/// use std::collections::HashSet;
/// use std::iter::FromIterator;
///
/// let mut state = State::new(
///     Weights::new(vec![(0, 1.0)].into_iter().collect()),
///     0.0,
///     LatestMessages::empty(),
///     2.0,
///     HashSet::new(),
/// );
///
/// state.update(&[
///     &VoteCount::create_vote_message(0, true),
///     &VoteCount::create_vote_message(0, false),
/// ]);
///
/// assert_eq!(
///     *state.latests_messages().get(&0).unwrap(),
///     HashSet::from_iter(vec![
///         VoteCount::create_vote_message(0, true),
///         VoteCount::create_vote_message(0, false),
///     ]),
/// );
/// assert_eq!(
///     *state.equivocators(),
///     HashSet::from_iter(vec![0]),
/// );
/// ```
#[derive(Debug, Clone)]
pub struct State<E, U>
where
    E: Estimator,
    U: WeightUnit,
{
    /// Current state total fault weight
    pub(crate) state_fault_weight: U,
    /// Fault tolerance threshold
    pub(crate) thr: U,
    /// Current validator set, mapped to their respective weights
    pub(crate) validators_weights: Weights<E::ValidatorName, U>,
    pub(crate) latest_messages: LatestMessages<E>,
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
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
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
        latest_messages: LatestMessages<E>,
        thr: U,
        equivocators: HashSet<E::ValidatorName>,
    ) -> Self {
        State {
            validators_weights,
            equivocators,
            state_fault_weight,
            thr,
            latest_messages,
        }
    }

    pub fn new_with_default_state(
        default_state: Self,
        validators_weights: Option<Weights<E::ValidatorName, U>>,
        state_fault_weight: Option<U>,
        latest_messages: Option<LatestMessages<E>>,
        thr: Option<U>,
        equivocators: Option<HashSet<E::ValidatorName>>,
    ) -> Self {
        State {
            validators_weights: validators_weights.unwrap_or(default_state.validators_weights),
            state_fault_weight: state_fault_weight.unwrap_or(default_state.state_fault_weight),
            latest_messages: latest_messages.unwrap_or(default_state.latest_messages),
            thr: thr.unwrap_or(default_state.thr),
            equivocators: equivocators.unwrap_or(default_state.equivocators),
        }
    }

    /// Adds messages to the state's latests_messages. Returns true if
    /// all messages added are valid latest messages.
    pub fn update(&mut self, messages: &[&Message<E>]) -> bool {
        messages.iter().fold(true, |acc, message| {
            let sender = message.sender();
            let weight = self
                .validators_weights
                .weight(sender)
                .unwrap_or(U::INFINITY);

            let update_success = self.latest_messages.update(message);

            if self.latest_messages.equivocate(message)
                && weight + self.state_fault_weight <= self.thr
                && self.equivocators.insert(sender.clone())
            {
                self.state_fault_weight += weight;
            }

            acc && update_success
        })
    }

    pub fn equivocators(&self) -> &HashSet<E::ValidatorName> {
        &self.equivocators
    }

    pub fn validators_weights(&self) -> &Weights<E::ValidatorName, U> {
        &self.validators_weights
    }

    pub fn latests_messages(&self) -> &LatestMessages<E> {
        &self.latest_messages
    }

    pub fn latests_messages_as_mut(&mut self) -> &mut LatestMessages<E> {
        &mut self.latest_messages
    }

    pub fn fault_weight(&self) -> U {
        self.state_fault_weight
    }

    /// Returns a vector containing sorted messages. They are sorted by the fault weight they would
    /// introduce in the state. If they would not be introduced because their validators are either
    /// honest or already equivocating, they are tie-breaked using the messages' hashes.
    pub fn sort_by_faultweight<'z>(
        &self,
        messages: &HashSet<&'z Message<E>>,
    ) -> Vec<&'z Message<E>> {
        let mut messages_sorted_by_faultw: Vec<_> = messages
            .iter()
            .filter_map(|&message| {
                // equivocations in relation to state
                let sender = message.sender();
                if !self.equivocators.contains(sender) && self.latest_messages.equivocate(message) {
                    self.validators_weights
                        .weight(sender)
                        .map(|weight| (message, weight))
                        .ok()
                } else {
                    Some((message, <U as Zero<U>>::ZERO))
                }
            })
            .collect();

        messages_sorted_by_faultw.sort_unstable_by(|(m0, w0), (m1, w1)| match w0.partial_cmp(w1) {
            None | Some(Ordering::Equal) => m0.id().cmp(&m1.id()),
            Some(ord) => ord,
        });

        messages_sorted_by_faultw
            .iter()
            .map(|(message, _)| message)
            .cloned()
            .collect()
    }
}

/// This type maps validators ([`ValidatorName`]) with their weights ([`WeightUnit`]).
///
/// [`ValidatorName`]: trait.ValidatorName.html
/// [`WeightUnit`]: ../util/weight/trait.WeightUnit.html
///
/// # Example
///
/// ```
/// use core_cbc_casper::validator::Weights;
///
/// let weights = Weights::new(vec![(0, 1.0), (1, 2.0), (2, 4.0)].into_iter().collect());
///
/// assert_eq!(
///     weights.sum_all_weights(),
///     7.0,
/// );
/// ```
#[derive(Clone, Debug)]
pub struct Weights<V: self::ValidatorName, U: WeightUnit>(Arc<RwLock<HashMap<V, U>>>);

impl<V: self::ValidatorName, U: WeightUnit> Weights<V, U> {
    /// Creates a new `Weights` struct from a `HashMap` of `ValidatorName` to `WeightUnit`.
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

    /// Returns success of insertion. Failure happens if we cannot acquire the lock to write data.
    pub fn insert(&mut self, validator: V, weight: U) -> Result<bool, Error<HashMap<V, U>>> {
        self.write()
            .map_err(Error::WriteLockError)
            .map(|mut hash_map| {
                hash_map.insert(validator, weight);
                true
            })
    }

    /// Picks validators with positive weights strictly greater than zero.
    /// Failure happens if we cannot acquire the lock to read data.
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

    /// Returns the total weight of all the validators in `self`.
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
            LatestMessages::empty(),
            2.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_message(0, false);
        let v1 = VoteCount::create_vote_message(1, true);

        let all_valid = validator_state.update(&[&v0, &v1]);

        let hs0 = validator_state
            .latests_messages()
            .get(&0)
            .expect("state should contain validator 0");
        let hs1 = validator_state
            .latests_messages()
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
            LatestMessages::empty(),
            2.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_message(0, false);
        let v0_prime = VoteCount::create_vote_message(0, true);
        let v1 = VoteCount::create_vote_message(1, true);

        let all_valid = validator_state.update(&[&v0, &v0_prime, &v1]);

        let hs0 = validator_state
            .latests_messages()
            .get(&0)
            .expect("state should contain validator 0");
        let hs1 = validator_state
            .latests_messages()
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
            LatestMessages::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_message(0, false);
        let v0_prime = VoteCount::create_vote_message(0, true);
        let v1 = VoteCount::create_vote_message(1, true);

        let all_valid = validator_state.update(&[&v0, &v0_prime, &v1]);

        let hs0 = validator_state
            .latests_messages()
            .get(&0)
            .expect("state should contain validator 0");
        let hs1 = validator_state
            .latests_messages()
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

    #[test]
    fn state_sort_by_faultweight_unknown_equivocators() {
        let v0_prime = VoteCount::create_vote_message(0, false);
        let v1_prime = VoteCount::create_vote_message(1, true);
        let v2_prime = VoteCount::create_vote_message(2, true);

        let get_sorted_vec_with_weights = |weights: Vec<(u32, f32)>| {
            let mut state = State::new(
                Weights::new(weights.into_iter().collect()),
                0.0,
                LatestMessages::empty(),
                10.0,
                HashSet::new(),
            );
            let v0 = VoteCount::create_vote_message(0, true);
            let v1 = VoteCount::create_vote_message(1, false);
            let v2 = VoteCount::create_vote_message(2, false);
            state.update(&[&v0, &v1, &v2]);
            state.sort_by_faultweight(&HashSet::from_iter(vec![&v0_prime, &v1_prime, &v2_prime]))
        };

        // As v0_prime, v1_prime and v2_prime would change the fault weight, the weight of their
        // validators influence the sort.
        assert_eq!(
            get_sorted_vec_with_weights(vec![(0, 1.0), (1, 2.0), (2, 3.0)]),
            [&v0_prime, &v1_prime, &v2_prime]
        );
        assert_eq!(
            get_sorted_vec_with_weights(vec![(0, 2.0), (1, 1.0), (2, 3.0)]),
            [&v1_prime, &v0_prime, &v2_prime]
        );
    }

    #[test]
    fn state_sort_by_faultweight_known_equivocators() {
        fn test_with_weights(weights: Vec<(u32, f32)>) {
            let mut state = State::new(
                Weights::new(weights.into_iter().collect()),
                0.0,
                LatestMessages::empty(),
                10.0,
                HashSet::new(),
            );
            let v0 = VoteCount::create_vote_message(0, true);
            let v0_prime = VoteCount::create_vote_message(0, false);
            let v1 = VoteCount::create_vote_message(1, false);
            let v1_prime = VoteCount::create_vote_message(1, true);
            let v2 = VoteCount::create_vote_message(2, false);
            let v2_prime = VoteCount::create_vote_message(2, true);
            state.update(&[&v0, &v0_prime, &v1, &v1_prime, &v2, &v2_prime]);

            // As all three validators are known equivocators and they could not change the current
            // fault weight, they are sorted by the tie-breaker. This means they are sorted by the
            // messages' hashes.
            assert_eq!(
                state.sort_by_faultweight(&HashSet::from_iter(vec![&v0, &v1, &v2])),
                [&v2, &v0, &v1]
            );

            // Comparing the hashes
            assert!(v2.id() < v0.id());
            assert!(v0.id() < v1.id());
        }

        // Weights have no influence
        test_with_weights(vec![(0, 2.0), (1, 1.0), (2, 3.0)]);
        test_with_weights(vec![(0, 2.0), (1, 4.0), (2, 3.0)]);
    }

    #[test]
    fn state_sort_by_faultweight_no_fault() {
        fn test_with_weights(weights: Vec<(u32, f32)>) {
            let mut state = State::new(
                Weights::new(weights.into_iter().collect()),
                0.0,
                LatestMessages::empty(),
                1.0,
                HashSet::new(),
            );
            let v0 = VoteCount::create_vote_message(0, true);
            let v1 = VoteCount::create_vote_message(1, false);
            let v2 = VoteCount::create_vote_message(2, false);
            state.update(&[&v0, &v1, &v2]);

            // As all three validators haven't equivocated, they are sorted by the tie-breaker.
            // This means they are sorted by the messages' hashes.
            assert_eq!(
                state.sort_by_faultweight(&HashSet::from_iter(vec![&v0, &v1, &v2])),
                [&v2, &v0, &v1]
            );

            // Comparing the hashes
            assert!(v2.id() < v0.id());
            assert!(v0.id() < v1.id());
        }

        // Weights have no influence
        test_with_weights(vec![(0, 2.0), (1, 1.0), (2, 3.0)]);
        test_with_weights(vec![(0, 2.0), (1, 4.0), (2, 3.0)]);
    }
}
