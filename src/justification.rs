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

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Formatter};

use rayon::iter::IntoParallelRefIterator;

use crate::estimator::Estimator;
use crate::message::Message;
use crate::util::weight::{WeightUnit, Zero};
use crate::validator;

/// This struct holds the set of the `message::Message` that justify
/// the current message. It works like a `Vec`.
#[derive(Eq, PartialEq, Clone, Hash)]
pub struct Justification<E: Estimator>(Vec<Message<E>>);

impl<E: Estimator> Justification<E> {
    /// Creates an empty justification.
    pub fn empty() -> Self {
        Justification(Vec::new())
    }

    /// Creates and returns a new justification from a vector of
    /// `message::Message` and mutates the given `validator::State`
    /// with the updated state.
    pub fn from_messages<U: WeightUnit>(
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

    pub fn contains(&self, message: &Message<E>) -> bool {
        self.0.contains(message)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// This function checks if the message is already contained into the underlying `Vec`. If it
    /// is, it does nothing and returns false. Else, it will push the message in the `Vec` and
    /// returns true.
    pub fn insert(&mut self, message: Message<E>) -> bool {
        if self.contains(&message) {
            false
        } else {
            self.0.push(message);
            true
        }
    }

    /// Runs the estimator on the justification given the set of equivocators and validators'
    /// weights.
    pub fn make_estimate<U: WeightUnit>(
        &self,
        equivocators: &HashSet<E::ValidatorName>,
        validators_weights: &validator::Weights<E::ValidatorName, U>,
    ) -> Result<E, E::Error> {
        let latest_messages = LatestMessages::from(self);
        let latest_messages_honest =
            LatestMessagesHonest::from_latest_messages(&latest_messages, equivocators);
        Estimator::estimate(&latest_messages_honest, validators_weights)
    }

    /// Inserts messages to the justification, accepting up to the threshold faults by weight.
    /// In ordering to insert as much messages as possible, the input messages are sorted
    /// ascendingly by their validators' weight.
    /// Returns a `HashSet` of messages that got successfully included in the justification.
    pub fn faulty_inserts<'a, U: WeightUnit>(
        &mut self,
        messages: &HashSet<&'a Message<E>>,
        state: &mut validator::State<E, U>,
    ) -> HashSet<&'a Message<E>> {
        let messages = state.sort_by_faultweight(messages);
        // do the actual insertions to the state
        messages
            .into_iter()
            .filter(|message| self.faulty_insert(message, state))
            .collect()
    }

    /// This function makes no assumption on how to treat the equivocator. It adds the message to
    /// the justification only if it will not cross the fault tolerance threshold.
    pub fn faulty_insert<U: WeightUnit>(
        &mut self,
        message: &Message<E>,
        state: &mut validator::State<E, U>,
    ) -> bool {
        let is_equivocation = state.latest_messages.equivocate(message);

        let sender = message.sender();
        let validator_weight = state
            .validators_weights
            .weight(sender)
            .unwrap_or(U::INFINITY);

        let already_in_equivocators = state.equivocators.contains(sender);

        match (is_equivocation, already_in_equivocators) {
            // if it's already equivocating and listed as such, or not equivocating at all, an
            // insertion can be done without more checks
            (false, _) | (true, true) => {
                let success = self.insert(message.clone());
                if success {
                    state.latest_messages.update(message);
                }
                success
            }
            // in the other case, we have to check that the threshold is not reached
            (true, false) => {
                if validator_weight + state.state_fault_weight <= state.thr {
                    let success = self.insert(message.clone());
                    if success {
                        state.latest_messages.update(message);
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

    /// This function sets the weight of an equivocator to zero right away (returned in
    /// `validator::State`) and add his message to the state, since his weight is null and doesn't
    /// count to the state fault weight anymore.
    pub fn faulty_insert_with_slash<'a, U: WeightUnit>(
        &mut self,
        message: &Message<E>,
        state: &'a mut validator::State<E, U>,
    ) -> Result<bool, validator::Error<'a, HashMap<E::ValidatorName, U>>> {
        let is_equivocation = state.latest_messages.equivocate(message);
        if is_equivocation {
            let sender = message.sender();
            state.equivocators.insert(sender.clone());
            state
                .validators_weights
                .insert(sender.clone(), <U as Zero<U>>::ZERO)?;
        }
        state.latest_messages.update(message);
        let success = self.insert(message.clone());
        Ok(success)
    }
}

impl<E: Estimator> From<LatestMessagesHonest<E>> for Justification<E> {
    fn from(lmh: LatestMessagesHonest<E>) -> Self {
        let mut justification = Self::empty();
        for message in lmh.iter() {
            justification.insert(message.clone());
        }
        justification
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
pub struct LatestMessages<E: Estimator>(HashMap<E::ValidatorName, HashSet<Message<E>>>);

impl<E: Estimator> LatestMessages<E> {
    /// Create an empty set of latest messages.
    pub fn empty() -> Self {
        LatestMessages(HashMap::new())
    }

    /// Insert a new set of messages for a validator.
    pub fn insert(
        &mut self,
        validator: E::ValidatorName,
        messages: HashSet<Message<E>>,
    ) -> Option<HashSet<Message<E>>> {
        self.0.insert(validator, messages)
    }

    /// Checks whether a sender is already contained in the map.
    pub fn contains_key(&self, validator: &E::ValidatorName) -> bool {
        self.0.contains_key(validator)
    }

    /// Get a set of messages sent by the validator.
    pub fn get(&self, validator: &E::ValidatorName) -> Option<&HashSet<Message<E>>> {
        self.0.get(validator)
    }

    /// Get a mutable set of messages sent by the validator.
    pub fn get_mut(
        &mut self,
        validator: &<E as Estimator>::ValidatorName,
    ) -> Option<&mut HashSet<Message<E>>> {
        self.0.get_mut(validator)
    }

    /// Get an iterator over the map.
    pub fn iter(&self) -> std::collections::hash_map::Iter<E::ValidatorName, HashSet<Message<E>>> {
        self.0.iter()
    }

    /// Get the map size.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Get the map keys, i.e. the validators.
    pub fn keys(&self) -> std::collections::hash_map::Keys<E::ValidatorName, HashSet<Message<E>>> {
        self.0.keys()
    }

    /// Get the map values, i.e. the messages.
    pub fn values(
        &self,
    ) -> std::collections::hash_map::Values<E::ValidatorName, HashSet<Message<E>>> {
        self.0.values()
    }

    /// Updates the data structure by adding a new message. Returns true if the new message is a
    /// valid latest message, i.e. the first message of a validator or a message that is not in the
    /// justification of the existing latest messages.
    pub fn update(&mut self, new_message: &Message<E>) -> bool {
        let sender = new_message.sender();
        if let Some(latest_messages_from_sender) = self.get(sender).cloned() {
            latest_messages_from_sender
                .iter()
                .filter(|&old_message| new_message != old_message)
                .fold(false, |acc, old_message| {
                    let new_independent_from_old = !new_message.depends(old_message);
                    // equivocation, old and new do not depend on each other
                    if new_independent_from_old && !old_message.depends(new_message) {
                        self.get_mut(sender)
                            .map(|messages| messages.insert(new_message.clone()))
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
                            .map(|messages| {
                                messages.remove(old_message) && messages.insert(new_message.clone())
                            })
                            .unwrap_or(false)
                            || acc
                    }
                })
        } else {
            // no message found for this validator, so new_message is the latest
            self.insert(
                sender.clone(),
                [new_message.clone()].iter().cloned().collect(),
            );
            true
        }
    }

    /// Checks whether the new message equivocates with any of the latest messages.
    pub(crate) fn equivocate(&self, message_new: &Message<E>) -> bool {
        self.get(message_new.sender())
            .map(|latest_messages| {
                latest_messages
                    .iter()
                    .any(|message| message.equivocates(&message_new))
            })
            .unwrap_or(false)
    }
}

impl<E: Estimator> From<&Justification<E>> for LatestMessages<E> {
    /// Extracts the latest messages of each validator from a justification.
    fn from(justification: &Justification<E>) -> Self {
        let mut latest_messages: LatestMessages<E> = LatestMessages::empty();
        let mut queue: VecDeque<Message<E>> = justification.iter().cloned().collect();
        while let Some(message) = queue.pop_front() {
            if latest_messages.update(&message) {
                message
                    .justification()
                    .iter()
                    .for_each(|message| queue.push_back(message.clone()));
            }
        }
        latest_messages
    }
}

/// Set of latest honest messages for each validator.
#[derive(Clone)]
pub struct LatestMessagesHonest<E: Estimator>(HashSet<Message<E>>);

impl<E: Estimator> LatestMessagesHonest<E> {
    /// Create an empty latest honest messages set.
    fn empty() -> Self {
        LatestMessagesHonest(HashSet::new())
    }

    /// Inserts a message in the set.
    fn insert(&mut self, message: Message<E>) -> bool {
        self.0.insert(message)
    }

    /// Removes the messages from a validator.
    pub fn remove(&mut self, validator: &E::ValidatorName) {
        self.0.retain(|message| message.sender() != validator);
    }

    /// Filters the latest messages to retrieve the latest honest messages and remove equivocators.
    pub fn from_latest_messages(
        latest_messages: &LatestMessages<E>,
        equivocators: &HashSet<E::ValidatorName>,
    ) -> Self {
        latest_messages
            .iter()
            .filter_map(|(validator, messages)| {
                if equivocators.contains(validator) || messages.len() != 1 {
                    None
                } else {
                    messages.iter().next()
                }
            })
            .fold(LatestMessagesHonest::empty(), |mut acc, message| {
                acc.insert(message.clone());
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

    pub fn make_estimate<U: WeightUnit>(
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

    use crate::justification::{Justification, LatestMessages};
    use crate::message::Message;
    use crate::validator;

    #[test]
    fn faulty_insert_sorted() {
        let v0 = VoteCount::create_vote_message(0, false);
        let v0_prime = VoteCount::create_vote_message(0, true);
        let v1 = VoteCount::create_vote_message(1, true);
        let v1_prime = VoteCount::create_vote_message(1, false);
        let v2 = VoteCount::create_vote_message(2, true);
        let v2_prime = VoteCount::create_vote_message(2, false);

        let mut latest_messages = LatestMessages::empty();
        latest_messages.update(&v0);
        latest_messages.update(&v1);
        latest_messages.update(&v2);

        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 2.0), (2, 3.0)].into_iter().collect()),
            0.0,
            latest_messages,
            3.0,
            HashSet::new(),
        );
        let mut justification = Justification::empty();
        let sorted_messages = validator_state
            .sort_by_faultweight(&vec![&v2_prime, &v1_prime, &v0_prime].into_iter().collect());

        sorted_messages.iter().for_each(|&message| {
            justification.faulty_insert(message, &mut validator_state);
        });

        assert_eq!(
            HashSet::<&Message<VoteCount>>::from_iter(justification.iter()),
            HashSet::from_iter(vec![&v0_prime, &v1_prime])
        );
        float_eq!(validator_state.fault_weight(), 3.0);
        assert_eq!(
            *validator_state.latests_messages().get(&0).unwrap(),
            HashSet::from_iter(vec![v0, v0_prime]),
        );
        assert_eq!(
            *validator_state.latests_messages().get(&1).unwrap(),
            HashSet::from_iter(vec![v1, v1_prime]),
        );
        assert_eq!(
            *validator_state.latests_messages().get(&2).unwrap(),
            HashSet::from_iter(vec![v2]),
        );
    }

    #[test]
    fn faulty_inserts() {
        let v0 = VoteCount::create_vote_message(0, false);
        let v0_prime = VoteCount::create_vote_message(0, true);
        let v1 = VoteCount::create_vote_message(1, true);
        let v1_prime = VoteCount::create_vote_message(1, false);
        let v2 = VoteCount::create_vote_message(2, true);
        let v2_prime = VoteCount::create_vote_message(2, false);

        let mut latest_messages = LatestMessages::empty();
        latest_messages.update(&v0);
        latest_messages.update(&v1);
        latest_messages.update(&v2);

        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 2.0), (2, 3.0)].into_iter().collect()),
            0.0,
            latest_messages,
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
            *validator_state.latests_messages().get(&0).unwrap(),
            HashSet::from_iter(vec![v0, v0_prime]),
        );
        assert_eq!(
            *validator_state.latests_messages().get(&1).unwrap(),
            HashSet::from_iter(vec![v1, v1_prime]),
        );
        assert_eq!(
            *validator_state.latests_messages().get(&2).unwrap(),
            HashSet::from_iter(vec![v2]),
        );
    }

    fn faulty_insert_setup() -> (Message<VoteCount>, validator::State<VoteCount, f32>) {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0)].into_iter().collect()),
            0.0,
            LatestMessages::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_message(0, false);
        let v0_prime = VoteCount::create_vote_message(0, true); // equivocating vote
        let v1 = VoteCount::create_vote_message(1, true);

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
        assert!(state
            .latests_messages()
            .get(&0)
            .unwrap()
            .contains(&v0_prime));
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
            state
                .latests_messages()
                .get(&0)
                .unwrap()
                .contains(&v0_prime),
            "$v0_prime$ should still be contained in $state.latests_messages()$",
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
        assert!(state
            .latests_messages()
            .get(&0)
            .unwrap()
            .contains(&v0_prime));
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
            state
                .latests_messages()
                .get(&0)
                .unwrap()
                .contains(&v0_prime),
            "$v0_prime$ should still be contained in $state.latests_messages()$",
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
            LatestMessages::empty(),
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
            LatestMessages::empty(),
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
            *validator_state.latests_messages().get(&0).unwrap(),
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
            LatestMessages::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_message(0, true);
        let v0_prime = VoteCount::create_vote_message(0, false);

        validator_state.update(&[&v0]);
        let v0_second = Message::from_validator_state(0, &validator_state).unwrap();

        assert!(validator_state.latests_messages().equivocate(&v0_prime));
        assert!(!validator_state.latests_messages().equivocate(&v0_second));
    }

    #[test]
    fn from_messages() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect()),
            0.0,
            LatestMessages::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_message(0, true);
        let v1 = VoteCount::create_vote_message(1, true);
        let v2 = VoteCount::create_vote_message(2, false);

        let initial_messages = vec![v0.clone(), v1.clone(), v2.clone()];
        let justification = Justification::from_messages(initial_messages, &mut validator_state);

        assert_eq!(
            HashSet::<&Message<VoteCount>>::from_iter(justification.iter()),
            HashSet::from_iter(vec![&v0, &v1, &v2]),
        );
    }

    #[test]
    fn from_messages_equivocation() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect()),
            0.0,
            LatestMessages::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_message(0, true);
        let v1 = VoteCount::create_vote_message(1, true);
        let v2 = VoteCount::create_vote_message(2, false);
        let v0_prime = VoteCount::create_vote_message(0, false);

        let initial_messages = vec![v0.clone(), v1.clone(), v2.clone()];
        let mut justification =
            Justification::from_messages(initial_messages, &mut validator_state);

        justification.faulty_insert(&v0_prime, &mut validator_state);

        assert_eq!(
            HashSet::<&Message<VoteCount>>::from_iter(justification.iter()),
            HashSet::from_iter(vec![&v0, &v1, &v2]),
        );
    }

    #[test]
    fn from_messages_duplicate() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0)].into_iter().collect()),
            0.0,
            LatestMessages::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_message(0, true);
        let v0_prime = VoteCount::create_vote_message(0, true);

        let initial_messages = vec![v0, v0_prime];

        let justification = Justification::from_messages(initial_messages, &mut validator_state);
        assert_eq!(
            justification.len(),
            1,
            "Justification should deduplicate messages"
        );
    }

    #[test]
    fn justification_make_estimate() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect()),
            0.0,
            LatestMessages::empty(),
            1.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_message(0, true);
        let v1 = VoteCount::create_vote_message(1, true);
        let v2 = VoteCount::create_vote_message(2, false);

        let initial_messages = vec![v0, v1, v2];
        let justification = Justification::from_messages(initial_messages, &mut validator_state);

        let estimate = justification.make_estimate(
            validator_state.equivocators(),
            validator_state.validators_weights(),
        );

        assert_eq!(
            estimate.expect("Estimate failed"),
            VoteCount { yes: 2, no: 1 }
        );
    }

    #[test]
    fn justification_make_estimate_equivocator_not_at_threshold() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect()),
            0.0,
            LatestMessages::empty(),
            1.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_message(0, true);
        let v0_prime = VoteCount::create_vote_message(0, false);
        let v1 = VoteCount::create_vote_message(1, false);
        let v2 = VoteCount::create_vote_message(2, false);

        let initial_messages = vec![v0, v1, v2];
        let mut justification =
            Justification::from_messages(initial_messages, &mut validator_state);
        justification.faulty_insert(&v0_prime, &mut validator_state);

        let estimate = justification.make_estimate(
            validator_state.equivocators(),
            validator_state.validators_weights(),
        );

        assert_eq!(
            estimate.expect("Estimate failed"),
            VoteCount { yes: 0, no: 2 }
        );
    }

    #[test]
    fn justification_make_estimate_equivocator_at_threshold() {
        let mut validator_state = validator::State::new(
            validator::Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect()),
            0.0,
            LatestMessages::empty(),
            0.0,
            HashSet::new(),
        );

        let v0 = VoteCount::create_vote_message(0, true);
        let v0_prime = VoteCount::create_vote_message(0, false);
        let v1 = VoteCount::create_vote_message(1, false);
        let v2 = VoteCount::create_vote_message(2, false);

        let initial_messages = vec![v0, v1, v2];
        let mut justification =
            Justification::from_messages(initial_messages, &mut validator_state);
        justification.faulty_insert(&v0_prime, &mut validator_state);

        let estimate = justification.make_estimate(
            validator_state.equivocators(),
            validator_state.validators_weights(),
        );

        assert_eq!(
            estimate.expect("Estimate failed"),
            VoteCount { yes: 1, no: 2 }
        );
    }

    #[test]
    fn latest_messages_update_new_sender() {
        let mut latest_messages = LatestMessages::empty();

        let v0 = VoteCount::create_vote_message(0, true);

        let sender_latest_messages_hashset = vec![v0.clone()].into_iter().collect();
        assert!(latest_messages.update(&v0));
        assert_eq!(
            latest_messages.get(&0),
            Some(&sender_latest_messages_hashset)
        );
    }

    #[test]
    fn latest_messages_update_duplicate_message() {
        let mut latest_messages = LatestMessages::empty();
        let v0 = VoteCount::create_vote_message(0, true);

        assert!(latest_messages.update(&v0));
        assert_eq!(
            latest_messages.get(&0),
            Some(&vec![v0.clone()].into_iter().collect())
        );
        assert!(!latest_messages.update(&v0.clone()));
        assert_eq!(
            latest_messages.get(&0),
            Some(&vec![v0].into_iter().collect())
        );
    }

    #[test]
    fn latest_messages_update_new_message() {
        let v0 = VoteCount::create_vote_message(0, false);
        let mut justification = Justification::empty();
        justification.insert(v0.clone());
        let v0_prime = Message::new(0, justification, VoteCount { yes: 1, no: 0 });

        let mut latest_messages = LatestMessages::empty();
        assert!(latest_messages.update(&v0));
        assert!(latest_messages.update(&v0_prime));

        assert_eq!(
            latest_messages.get(&0),
            Some(&vec![v0_prime].into_iter().collect())
        );
    }

    #[test]
    fn latest_messages_update_old_message() {
        // update will only return false in this case.
        let v0 = VoteCount::create_vote_message(0, false);
        let mut justification = Justification::empty();
        justification.insert(v0.clone());
        let v0_prime = Message::new(0, justification, VoteCount { yes: 1, no: 0 });

        let mut latest_messages = LatestMessages::empty();
        assert!(latest_messages.update(&v0_prime));
        assert!(!latest_messages.update(&v0));

        assert_eq!(
            latest_messages.get(&0),
            Some(&vec![v0_prime].into_iter().collect())
        );
    }

    #[test]
    fn latest_messages_update_equivocation() {
        let v0 = VoteCount::create_vote_message(0, false);
        let v0_prime = VoteCount::create_vote_message(0, true);

        let mut latest_messages = LatestMessages::empty();
        assert!(latest_messages.update(&v0));
        assert!(latest_messages.update(&v0_prime));

        assert_eq!(
            latest_messages.get(&0),
            Some(&vec![v0, v0_prime].into_iter().collect())
        );
    }
}
