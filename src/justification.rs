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

//! # Later Messages
//!
//! If message *A* is in the justification of message *B*, then message *B* is **later** than
//! message *A*.
//!
//! # Estimator Function
//!
//! The **estimator function takes the justification** (which is a set of messages) as input, and
//! **returns the set of consensus values** that are “justified” by the input.  For example, in an
//! integer consensus setting, the estimator will return integer values. In a blockchain setting,
//! the the estimator will return blocks which can be added on top of the current tip detected from
//! the blocks in the messages in the inputted justification.
//!
//! Source: [Casper CBC, Simplified!](https://medium.com/@aditya.asgaonkar/casper-cbc-simplified-2370922f9aa6),
//! by Aditya Asgaonkar.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Formatter};

use rayon::iter::IntoParallelRefIterator;

use crate::estimator::Estimator;
use crate::message::Message;
use crate::util::weight::{WeightUnit, Zero};
use crate::validator;

/// Struct that holds the set of the `message::Message` that justify
/// the current message. Works like a `vec`.
#[derive(Eq, PartialEq, Clone, Hash)]
pub struct Justification<E: Estimator>(Vec<Message<E>>);

impl<E: Estimator> Justification<E> {
    /// Create an empty justification.
    pub fn empty() -> Self {
        Justification(Vec::new())
    }

    /// Creates and returns a new justification from a vector of
    /// `message::Message` and mutates the given `validator::State`
    /// with the updated state.
    pub fn from_msgs<U: WeightUnit>(
        messages: Vec<Message<E>>,
        state: &mut validator::State<E, U>,
    ) -> Self {
        let mut justification = Justification::empty();
        let messages: HashSet<_> = messages.iter().collect();
        justification.faulty_inserts(&messages, state);
        justification
    }

    pub fn iter(&self) -> std::slice::Iter<Message<E>> {
        self.0.iter()
    }

    pub fn par_iter(&self) -> rayon::slice::Iter<Message<E>> {
        self.0.par_iter()
    }

    pub fn contains(&self, msg: &Message<E>) -> bool {
        self.0.contains(msg)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn insert(&mut self, msg: Message<E>) -> bool {
        if self.contains(&msg) {
            false
        } else {
            self.0.push(msg);
            true
        }
    }

    /// Run the estimator on the justification given the set of equivocators and validators' weights.
    pub fn mk_estimate<U: WeightUnit>(
        &self,
        equivocators: &HashSet<E::ValidatorName>,
        validators_weights: &validator::Weights<E::ValidatorName, U>,
    ) -> Result<E, E::Error> {
        let latest_msgs = LatestMsgs::from(self);
        let latest_msgs_honest = LatestMsgsHonest::from_latest_msgs(&latest_msgs, equivocators);
        Estimator::estimate(&latest_msgs_honest, validators_weights)
    }

    /// Insert messages to the justification, accepting up to the threshold faults by weight.
    /// Returns a HashSet of messages that got successfully included in the justification.
    pub fn faulty_inserts<'a, U: WeightUnit>(
        &mut self,
        msgs: &HashSet<&'a Message<E>>,
        state: &mut validator::State<E, U>,
    ) -> HashSet<&'a Message<E>> {
        let msgs = state.sort_by_faultweight(msgs);
        // do the actual insertions to the state
        msgs.into_iter()
            .filter(|msg| self.faulty_insert(msg, state))
            .collect()
    }

    /// This function makes no assumption on how to treat the equivocator. it adds the msg to the
    /// justification only if it will not cross the fault tolerance threshold.
    pub fn faulty_insert<U: WeightUnit>(
        &mut self,
        msg: &Message<E>,
        state: &mut validator::State<E, U>,
    ) -> bool {
        let is_equivocation = state.latest_msgs.equivocate(msg);

        let sender = msg.sender();
        let validator_weight = state
            .validators_weights
            .weight(sender)
            .unwrap_or(U::INFINITY);

        let already_in_equivocators = state.equivocators.contains(sender);

        match (is_equivocation, already_in_equivocators) {
            // if it's already equivocating and listed as such, or not equivocating at all, an
            // insertion can be done without more checks
            (false, _) | (true, true) => {
                let success = self.insert(msg.clone());
                if success {
                    state.latest_msgs.update(msg);
                }
                success
            }
            // in the other case, we have to check that the threshold is not reached
            (true, false) => {
                if validator_weight + state.state_fault_weight <= state.thr {
                    let success = self.insert(msg.clone());
                    if success {
                        state.latest_msgs.update(msg);
                        if state.equivocators.insert(sender.clone()) {
                            state.state_fault_weight += validator_weight;
                        }
                    }
                    success
                } else {
                    false
                }
            }
        }
    }

    /// This function sets the weight of the equivocator to zero right away (returned in
    /// `validator::State`) and add his message to the state, since now his equivocation doesnt count
    /// to the state fault weight anymore
    pub fn faulty_insert_with_slash<'a, U: WeightUnit>(
        &mut self,
        msg: &Message<E>,
        state: &'a mut validator::State<E, U>,
    ) -> Result<bool, validator::Error<'a, HashMap<E::ValidatorName, U>>> {
        let is_equivocation = state.latest_msgs.equivocate(msg);
        if is_equivocation {
            let sender = msg.sender();
            state.equivocators.insert(sender.clone());
            state
                .validators_weights
                .insert(sender.clone(), <U as Zero<U>>::ZERO)?;
        }
        state.latest_msgs.update(msg);
        let success = self.insert(msg.clone());
        Ok(success)
    }
}

impl<E: Estimator> From<LatestMsgsHonest<E>> for Justification<E> {
    fn from(lmh: LatestMsgsHonest<E>) -> Self {
        let mut j = Self::empty();
        for m in lmh.iter() {
            j.insert(m.clone());
        }
        j
    }
}

impl<E: Estimator> Debug for Justification<E> {
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// Mapping between validators and their latests messages. Latest messages from a validator are all
/// their messages that are not in the dependency of another of their messages.
#[derive(Eq, PartialEq, Clone, Debug)]
pub struct LatestMsgs<E: Estimator>(HashMap<E::ValidatorName, HashSet<Message<E>>>);

impl<E: Estimator> LatestMsgs<E> {
    /// Create an empty set of latest messages.
    pub fn empty() -> Self {
        LatestMsgs(HashMap::new())
    }

    /// Insert a new set of messages for a sender.
    pub fn insert(
        &mut self,
        k: E::ValidatorName,
        v: HashSet<Message<E>>,
    ) -> Option<HashSet<Message<E>>> {
        self.0.insert(k, v)
    }

    /// Checks whether a sender is already contained in the map.
    pub fn contains_key(&self, k: &E::ValidatorName) -> bool {
        self.0.contains_key(k)
    }

    /// Get a set of messages sent by the sender.
    pub fn get(&self, k: &E::ValidatorName) -> Option<&HashSet<Message<E>>> {
        self.0.get(k)
    }

    /// Get a mutable set of messages sent by the sender.
    pub fn get_mut(
        &mut self,
        k: &<E as Estimator>::ValidatorName,
    ) -> Option<&mut HashSet<Message<E>>> {
        self.0.get_mut(k)
    }

    /// Get an iterator on the set.
    pub fn iter(&self) -> std::collections::hash_map::Iter<E::ValidatorName, HashSet<Message<E>>> {
        self.0.iter()
    }

    /// Get the set size.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Get the set keys, i.e. the senders.
    pub fn keys(&self) -> std::collections::hash_map::Keys<E::ValidatorName, HashSet<Message<E>>> {
        self.0.keys()
    }

    /// Get the set values, i.e. the messages.
    pub fn values(
        &self,
    ) -> std::collections::hash_map::Values<'_, E::ValidatorName, HashSet<Message<E>>> {
        self.0.values()
    }

    /// Update the data structure by adding a new message. Return true if the new message is a
    /// valid latest message, i.e. the first message of a validator or a message that is not in the
    /// justification of the existing latest messages.
    pub fn update(&mut self, new_msg: &Message<E>) -> bool {
        let sender = new_msg.sender();
        if let Some(latest_msgs_from_sender) = self.get(sender).cloned() {
            latest_msgs_from_sender
                .iter()
                .filter(|&old_msg| new_msg != old_msg)
                .fold(false, |acc, old_msg| {
                    let new_independent_from_old = !new_msg.depends(old_msg);
                    // equivocation, old and new do not depend on each other
                    if new_independent_from_old && !old_msg.depends(new_msg) {
                        self.get_mut(sender)
                            .map(|msgs| msgs.insert(new_msg.clone()))
                            .unwrap_or(false)
                            || acc
                    }
                    // new actually older than old
                    else if new_independent_from_old {
                        acc
                    }
                    // new newer than old
                    else {
                        self.get_mut(sender)
                            .map(|msgs| msgs.remove(old_msg) && msgs.insert(new_msg.clone()))
                            .unwrap_or(false)
                            || acc
                    }
                })
        } else {
            // no message found for this validator, so new_msg is the latest
            self.insert(sender.clone(), [new_msg.clone()].iter().cloned().collect());
            true
        }
    }

    /// Checks whether the new message equivocates with latest messages.
    pub(crate) fn equivocate(&self, msg_new: &Message<E>) -> bool {
        self.get(msg_new.sender())
            .map(|latest_msgs| latest_msgs.iter().any(|m| m.equivocates(&msg_new)))
            .unwrap_or(false)
    }
}

impl<'z, E: Estimator> From<&'z Justification<E>> for LatestMsgs<E> {
    /// Extract the latest messages of each validator from a justification.
    fn from(j: &Justification<E>) -> Self {
        let mut latest_msgs: LatestMsgs<E> = LatestMsgs::empty();
        let mut queue: VecDeque<Message<E>> = j.iter().cloned().collect();
        while let Some(msg) = queue.pop_front() {
            if latest_msgs.update(&msg) {
                msg.justification()
                    .iter()
                    .for_each(|m| queue.push_back(m.clone()));
            }
        }
        latest_msgs
    }
}

/// Set of latest honest messages for each validator.
#[derive(Clone)]
pub struct LatestMsgsHonest<E: Estimator>(HashSet<Message<E>>);

impl<E: Estimator> LatestMsgsHonest<E> {
    /// Create an empty latest honest messages set.
    fn empty() -> Self {
        LatestMsgsHonest(HashSet::new())
    }

    /// Insert message to the set.
    fn insert(&mut self, msg: Message<E>) -> bool {
        self.0.insert(msg)
    }

    /// Remove messages of a validator.
    pub fn remove(&mut self, validator: &E::ValidatorName) {
        self.0.retain(|msg| msg.sender() != validator);
    }

    /// Filters the latest messages to retreive the latest honest messages and remove equivocators.
    pub fn from_latest_msgs(
        latest_msgs: &LatestMsgs<E>,
        equivocators: &HashSet<E::ValidatorName>,
    ) -> Self {
        latest_msgs
            .iter()
            .filter_map(|(validator, msgs)| {
                if equivocators.contains(validator) || msgs.len() != 1 {
                    None
                } else {
                    msgs.iter().next()
                }
            })
            .fold(LatestMsgsHonest::empty(), |mut acc, msg| {
                acc.insert(msg.clone());
                acc
            })
    }

    pub fn iter(&self) -> std::collections::hash_set::Iter<Message<E>> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn mk_estimate<U: WeightUnit>(
        &self,
        validators_weights: &validator::Weights<E::ValidatorName, U>,
    ) -> Result<E, E::Error> {
        E::estimate(&self, validators_weights)
    }
}

#[cfg(test)]
mod test {
    use crate::{IntegerWrapper, VoteCount};

    use std::collections::HashSet;
    use std::iter::FromIterator;

    use crate::justification::{Justification, LatestMsgs};
    use crate::message::Message;
    use crate::validator;

    #[test]
    fn faulty_insert_sorted() {
        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true);
        let v1 = VoteCount::create_vote_msg(1, true);
        let v1_prime = VoteCount::create_vote_msg(1, false);
        let v2 = VoteCount::create_vote_msg(2, true);
        let v2_prime = VoteCount::create_vote_msg(2, false);

        let mut latest_msgs = LatestMsgs::empty();
        latest_msgs.update(&v0);
        latest_msgs.update(&v1);
        latest_msgs.update(&v2);

        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 2.0), (2, 3.0)].into_iter().collect()),
            0.0,
            latest_msgs,
            3.0,
            HashSet::new(),
        );
        let mut justification = Justification::empty();
        let sorted_msgs = validator_state
            .sort_by_faultweight(&vec![&v2_prime, &v1_prime, &v0_prime].into_iter().collect());

        sorted_msgs.iter().for_each(|&m| {
            justification.faulty_insert(m, &mut validator_state);
        });

        assert_eq!(
            HashSet::<&Message<VoteCount>>::from_iter(justification.iter()),
            HashSet::from_iter(vec![&v0_prime, &v1_prime])
        );
        float_eq!(validator_state.fault_weight(), 3.0);
        assert_eq!(
            *validator_state.latests_msgs().get(&0).unwrap(),
            HashSet::from_iter(vec![v0, v0_prime]),
        );
        assert_eq!(
            *validator_state.latests_msgs().get(&1).unwrap(),
            HashSet::from_iter(vec![v1, v1_prime]),
        );
        assert_eq!(
            *validator_state.latests_msgs().get(&2).unwrap(),
            HashSet::from_iter(vec![v2]),
        );
    }

    #[test]
    fn faulty_inserts() {
        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true);
        let v1 = VoteCount::create_vote_msg(1, true);
        let v1_prime = VoteCount::create_vote_msg(1, false);
        let v2 = VoteCount::create_vote_msg(2, true);
        let v2_prime = VoteCount::create_vote_msg(2, false);

        let mut latest_msgs = LatestMsgs::empty();
        latest_msgs.update(&v0);
        latest_msgs.update(&v1);
        latest_msgs.update(&v2);

        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 2.0), (2, 3.0)].into_iter().collect()),
            0.0,
            latest_msgs,
            3.0,
            HashSet::new(),
        );
        let mut justification = Justification::empty();
        justification.faulty_inserts(
            &vec![&v2_prime, &v1_prime, &v0_prime].into_iter().collect(),
            &mut validator_state,
        );

        assert_eq!(
            HashSet::<&Message<VoteCount>>::from_iter(justification.iter()),
            HashSet::from_iter(vec![&v0_prime, &v1_prime])
        );
        float_eq!(validator_state.fault_weight(), 3.0);
        assert_eq!(
            *validator_state.latests_msgs().get(&0).unwrap(),
            HashSet::from_iter(vec![v0, v0_prime]),
        );
        assert_eq!(
            *validator_state.latests_msgs().get(&1).unwrap(),
            HashSet::from_iter(vec![v1, v1_prime]),
        );
        assert_eq!(
            *validator_state.latests_msgs().get(&2).unwrap(),
            HashSet::from_iter(vec![v2]),
        );
    }

    fn faulty_insert_setup() -> (Message<VoteCount>, validator::State<VoteCount, f32>) {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = VoteCount::create_vote_msg(1, true);

        let mut validator_state_clone = validator_state.clone();
        validator_state_clone.update(&[&v0]);
        let m0 = Message::from_validator_state(0, &validator_state_clone).unwrap();

        validator_state.update(&[&v1, &m0, &v0_prime]);

        (v0_prime, validator_state)
    }

    #[test]
    fn faulty_insert_accept_fault() {
        let (v0_prime, validator_state) = faulty_insert_setup();

        let mut state = validator::State::new_with_default_state(
            validator_state,
            None,
            None,
            None,
            Some(1.0),
            None,
        );
        let mut justification = Justification::empty();
        let success = justification.faulty_insert(&v0_prime, &mut state);

        assert!(
            success,
            "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it \
             doesnt cross the fault threshold for the set"
        );
        assert_eq!(justification.len(), 1);
        assert!(justification.contains(&v0_prime));
        assert!(state.latests_msgs().get(&0).unwrap().contains(&v0_prime));
        assert!(state.equivocators().contains(&0));
        float_eq!(
            state.fault_weight(),
            1.0,
            "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it \
             doesnt cross the fault threshold for the set, and thus the state_fault_weight should \
             be incremented to 1.0"
        );
    }

    #[test]
    fn faulty_insert_at_threshold() {
        let (v0_prime, validator_state) = faulty_insert_setup();

        let mut state = validator::State::new_with_default_state(
            validator_state,
            None,
            Some(0.1),
            None,
            Some(1.0),
            None,
        );
        let mut justification = Justification::empty();
        let success = justification.faulty_insert(&v0_prime, &mut state);

        assert!(
            !success,
            "$v0_prime$ conflicts with $v0$ through $m0$, and we should not accept this fault as \
             the fault threshold gets crossed for the set"
        );
        assert!(justification.is_empty());
        assert!(!justification.contains(&v0_prime));
        assert!(
            state.latests_msgs().get(&0).unwrap().contains(&v0_prime),
            "$v0_prime$ should still be contained in $state.latests_msgs()$",
        );
        assert!(!state.equivocators().contains(&0));
        float_eq!(
            state.fault_weight(),
            0.1,
            "$v0_prime$ conflicts with $v0$ through $m0$, and we should NOT accept this fault as \
             the fault threshold gets crossed for the set, and thus the state_fault_weight should \
             not be incremented"
        );
    }

    #[test]
    fn faulty_insert_accept_with_bigger_numbers() {
        let (v0_prime, validator_state) = faulty_insert_setup();

        let mut state = validator::State::new_with_default_state(
            validator_state,
            None,
            Some(1.0),
            None,
            Some(2.0),
            None,
        );
        let mut justification = Justification::empty();
        let success = justification.faulty_insert(&v0_prime, &mut state);

        assert!(
            success,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should accept this fault as the \
             threshold doesnt get crossed for the set"
        );
        assert!(!justification.is_empty());
        assert!(justification.contains(&v0_prime));
        assert!(state.latests_msgs().get(&0).unwrap().contains(&v0_prime));
        assert!(state.equivocators().contains(&0));
        float_eq!(
            state.fault_weight(),
            2.0,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as \
             we can't know the weight of the validator, which could be Infinity, and thus the \
             state_fault_weight should be unchanged"
        );
    }

    #[test]
    fn faulty_insert_unknown_weights() {
        let (v0_prime, validator_state) = faulty_insert_setup();

        // bug found
        let mut state = validator::State::new_with_default_state(
            validator_state,
            Some(validator::Weights::new(vec![].into_iter().collect())),
            Some(1.0),
            None,
            Some(2.0),
            None,
        );
        let mut justification = Justification::empty();
        let success = justification.faulty_insert(&v0_prime, &mut state);

        assert!(
            !success,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as \
             we can't know the weight of the validator, which could be Infinity"
        );
        assert!(justification.is_empty());
        assert!(!justification.contains(&v0_prime));
        assert!(
            state.latests_msgs().get(&0).unwrap().contains(&v0_prime),
            "$v0_prime$ should still be contained in $state.latests_msgs()$",
        );
        assert!(!state.equivocators().contains(&0));
        float_eq!(
            state.fault_weight(),
            1.0,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as \
             we can't know the weight of the validator, which could be Infinity, and thus the \
             state_fault_weight should be unchanged"
        );
    }

    #[test]
    fn faulty_insert_double_equivocation() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            1.0,
            HashSet::new(),
        );

        let v0 = Message::new(0, Justification::empty(), IntegerWrapper::new(0));
        let v0_prime = Message::new(0, Justification::empty(), IntegerWrapper::new(1));
        let v0_second = Message::new(0, Justification::empty(), IntegerWrapper::new(2));

        let mut justification = Justification::empty();

        // 0's equivocation can be registered as it would not cross the threshold. Its third
        // message would not change the fault weight and is also accepted.
        assert!(justification.faulty_insert(&v0, &mut validator_state));
        assert!(justification.faulty_insert(&v0_prime, &mut validator_state));
        assert!(justification.faulty_insert(&v0_second, &mut validator_state));

        assert_eq!(
            HashSet::<&Message<IntegerWrapper>>::from_iter(justification.iter()),
            HashSet::from_iter(vec![&v0, &v0_prime, &v0_second])
        );
        assert!(validator_state.equivocators().contains(&0));
        float_eq!(validator_state.fault_weight(), 1.0);
    }

    #[test]
    fn faulty_insert_with_slash() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            1.0,
            HashSet::new(),
        );

        let v0 = Message::new(0, Justification::empty(), IntegerWrapper::new(0));
        let v0_prime = Message::new(0, Justification::empty(), IntegerWrapper::new(1));

        let mut justification = Justification::empty();

        assert!(justification
            .faulty_insert_with_slash(&v0, &mut validator_state)
            .unwrap());
        assert!(justification
            .faulty_insert_with_slash(&v0_prime, &mut validator_state)
            .unwrap());

        assert!(justification.contains(&v0));
        assert!(justification.contains(&v0_prime));
        assert_eq!(
            *validator_state.latests_msgs().get(&0).unwrap(),
            HashSet::from_iter(vec![v0, v0_prime]),
        );
        assert_eq!(*validator_state.equivocators(), HashSet::from_iter(vec![0]));
        float_eq!(
            validator_state.validators_weights().weight(&0).unwrap(),
            0.0
        );
        float_eq!(validator_state.fault_weight(), 0.0);
    }

    #[test]
    fn equivocate() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_msg(0, true);
        let v0_prime = VoteCount::create_vote_msg(0, false);

        validator_state.update(&[&v0]);
        let v0_second = Message::from_validator_state(0, &validator_state).unwrap();

        assert!(validator_state.latests_msgs().equivocate(&v0_prime));
        assert!(!validator_state.latests_msgs().equivocate(&v0_second));
    }

    #[test]
    fn from_msgs() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_msg(0, true);
        let v1 = VoteCount::create_vote_msg(1, true);
        let v2 = VoteCount::create_vote_msg(2, false);

        let initial_msgs = vec![v0.clone(), v1.clone(), v2.clone()];
        let justification = Justification::from_msgs(initial_msgs, &mut validator_state);

        assert_eq!(
            HashSet::<&Message<VoteCount>>::from_iter(justification.iter()),
            HashSet::from_iter(vec![&v0, &v1, &v2]),
        );
    }

    #[test]
    fn from_msgs_equivocation() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_msg(0, true);
        let v1 = VoteCount::create_vote_msg(1, true);
        let v2 = VoteCount::create_vote_msg(2, false);
        let v0_prime = VoteCount::create_vote_msg(0, false);

        let initial_msgs = vec![v0.clone(), v1.clone(), v2.clone()];
        let mut justification = Justification::from_msgs(initial_msgs, &mut validator_state);

        justification.faulty_insert(&v0_prime, &mut validator_state);

        assert_eq!(
            HashSet::<&Message<VoteCount>>::from_iter(justification.iter()),
            HashSet::from_iter(vec![&v0, &v1, &v2]),
        );
    }

    #[test]
    fn from_msgs_duplicate() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_msg(0, true);
        let v0_prime = VoteCount::create_vote_msg(0, true);

        let initial_msgs = vec![v0, v0_prime];

        let justification = Justification::from_msgs(initial_msgs, &mut validator_state);
        assert_eq!(
            justification.len(),
            1,
            "Justification should deduplicate messages"
        );
    }

    #[test]
    fn justification_mk_estimate() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            1.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_msg(0, true);
        let v1 = VoteCount::create_vote_msg(1, true);
        let v2 = VoteCount::create_vote_msg(2, false);

        let initial_msgs = vec![v0, v1, v2];
        let justification = Justification::from_msgs(initial_msgs, &mut validator_state);

        let estimate = justification.mk_estimate(
            validator_state.equivocators(),
            validator_state.validators_weights(),
        );

        assert_eq!(
            estimate.expect("Estimate failed"),
            VoteCount { yes: 2, no: 1 }
        );
    }

    #[test]
    fn justification_mk_estimate_equivocator_not_at_threshold() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            1.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_msg(0, true);
        let v0_prime = VoteCount::create_vote_msg(0, false);
        let v1 = VoteCount::create_vote_msg(1, false);
        let v2 = VoteCount::create_vote_msg(2, false);

        let initial_msgs = vec![v0, v1, v2];
        let mut justification = Justification::from_msgs(initial_msgs, &mut validator_state);
        justification.faulty_insert(&v0_prime, &mut validator_state);

        let estimate = justification.mk_estimate(
            validator_state.equivocators(),
            validator_state.validators_weights(),
        );

        assert_eq!(
            estimate.expect("Estimate failed"),
            VoteCount { yes: 0, no: 2 }
        );
    }

    #[test]
    fn justification_mk_estimate_equivocator_at_threshold() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect()),
            0.0,
            LatestMsgs::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_msg(0, true);
        let v0_prime = VoteCount::create_vote_msg(0, false);
        let v1 = VoteCount::create_vote_msg(1, false);
        let v2 = VoteCount::create_vote_msg(2, false);

        let initial_msgs = vec![v0, v1, v2];
        let mut justification = Justification::from_msgs(initial_msgs, &mut validator_state);
        justification.faulty_insert(&v0_prime, &mut validator_state);

        let estimate = justification.mk_estimate(
            validator_state.equivocators(),
            validator_state.validators_weights(),
        );

        assert_eq!(
            estimate.expect("Estimate failed"),
            VoteCount { yes: 1, no: 2 }
        );
    }

    #[test]
    fn latest_msgs_update_new_sender() {
        let mut latest_msgs = LatestMsgs::empty();

        let v0 = VoteCount::create_vote_msg(0, true);

        let sender_latest_msgs_hashset = vec![v0.clone()].into_iter().collect();
        assert!(latest_msgs.update(&v0));
        assert_eq!(latest_msgs.get(&0), Some(&sender_latest_msgs_hashset));
    }

    #[test]
    fn latest_msgs_update_duplicate_msg() {
        let mut latest_msgs = LatestMsgs::empty();
        let v0 = VoteCount::create_vote_msg(0, true);

        assert!(latest_msgs.update(&v0));
        assert_eq!(
            latest_msgs.get(&0),
            Some(&vec![v0.clone()].into_iter().collect())
        );
        assert!(!latest_msgs.update(&v0.clone()));
        assert_eq!(latest_msgs.get(&0), Some(&vec![v0].into_iter().collect()));
    }

    #[test]
    fn latest_msgs_update_new_message() {
        let v0 = VoteCount::create_vote_msg(0, false);
        let mut justification = Justification::empty();
        justification.insert(v0.clone());
        let v0_prime = Message::new(0, justification, VoteCount { yes: 1, no: 0 });

        let mut latest_msgs = LatestMsgs::empty();
        assert!(latest_msgs.update(&v0));
        assert!(latest_msgs.update(&v0_prime));

        assert_eq!(
            latest_msgs.get(&0),
            Some(&vec![v0_prime].into_iter().collect())
        );
    }

    #[test]
    fn latest_msgs_update_old_message() {
        // update will only return false in this case.
        let v0 = VoteCount::create_vote_msg(0, false);
        let mut justification = Justification::empty();
        justification.insert(v0.clone());
        let v0_prime = Message::new(0, justification, VoteCount { yes: 1, no: 0 });

        let mut latest_msgs = LatestMsgs::empty();
        assert!(latest_msgs.update(&v0_prime));
        assert!(!latest_msgs.update(&v0));

        assert_eq!(
            latest_msgs.get(&0),
            Some(&vec![v0_prime].into_iter().collect())
        );
    }

    #[test]
    fn latest_msgs_update_equivocation() {
        let v0 = VoteCount::create_vote_msg(0, false);
        let v0_prime = VoteCount::create_vote_msg(0, true);

        let mut latest_msgs = LatestMsgs::empty();
        assert!(latest_msgs.update(&v0));
        assert!(latest_msgs.update(&v0_prime));

        assert_eq!(
            latest_msgs.get(&0),
            Some(&vec![v0, v0_prime].into_iter().collect())
        );
    }
}
