// Core CBC Rust Library
// Copyright (C) 2018  pZ4 <pz4@protonmail.ch>,
//                     Lederstrumpf,
//                     h4sh3d <h4sh3d@truelevel.io>
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

use crate::message;
use crate::sender;
use crate::traits::{Estimate, Zero};
use crate::util::weight::{SendersWeight, WeightUnit};

/// Struct that holds the set of the message::Traits that justify
/// the current message
/// Works like a Vec
#[derive(Eq, PartialEq, Clone, Default, Hash)]
pub struct Justification<M: message::Trait>(Vec<M>);

impl<M: message::Trait> Justification<M> {
    /// Re-exports from Vec wrapping M
    pub fn new() -> Self {
        Justification(Vec::new())
    }

    /// creates a new Justification instance from a Vec of message::Trait
    /// and a sender::State
    pub fn from_msgs(msgs: Vec<M>, sender_state: &sender::State<M>) -> (Self, sender::State<M>) {
        let mut j = Justification::new();
        let msgs: HashSet<_> = msgs.iter().collect();
        let (_, sender_state) = j.faulty_inserts(msgs, sender_state);
        (j, sender_state)
    }

    pub fn iter(&self) -> std::slice::Iter<M> {
        self.0.iter()
    }

    pub fn par_iter(&self) -> rayon::slice::Iter<M> {
        self.0.par_iter()
    }

    pub fn contains(&self, msg: &M) -> bool {
        self.0.contains(msg)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn insert(&mut self, msg: M) -> bool {
        if self.contains(&msg)
        // || self.iter().any(|m| m.sender() == msg.sender())
        {
            false
        } else {
            self.0.push(msg);
            true
        }
    }

    /// reexport from Estimate impl
    pub fn mk_estimate(
        &self,
        equivocators: &HashSet<M::Sender>,
        senders_weights: &SendersWeight<<M as message::Trait>::Sender>,
        // data: Option<<<M as message::Trait>::Estimate as Data>::Data>,
    ) -> Result<M::Estimate, &'static str> {
        let latest_msgs = LatestMsgs::from(self);
        let latest_msgs_honest = LatestMsgsHonest::from_latest_msgs(&latest_msgs, equivocators);
        M::Estimate::mk_estimate(&latest_msgs_honest, senders_weights)
    }

    // Custom functions

    /// insert msgs to the Justification, accepting up to $thr$ faults by
    /// weight, returns success=true if at least one msg of the set gets
    /// successfully included in the justification
    pub fn faulty_inserts(
        &mut self,
        msgs: HashSet<&M>,
        sender_state: &sender::State<M>,
    ) -> (bool, sender::State<M>) {
        let msgs = sender_state.sort_by_faultweight(msgs);
        // do the actual insertions to the state
        msgs.iter().fold(
            (false, sender_state.clone()),
            |(success, sender_state), &msg| {
                let (success_prime, sender_state_prime) = self.faulty_insert(msg, &sender_state);
                (success || success_prime, sender_state_prime)
            },
        )
    }

    /// this function makes no assumption on how to treat the equivocator. it
    /// adds the msg to the justification only if it will not cross the fault
    /// tolerance thr
    pub fn faulty_insert(
        &mut self,
        msg: &M,
        sender_state: &sender::State<M>,
    ) -> (bool, sender::State<M>) {
        let mut sender_state = sender_state.clone();
        let is_equivocation = sender_state.latest_msgs.equivocate(msg);

        let sender = msg.sender();
        let sender_weight = sender_state
            .senders_weights
            .weight(sender)
            .unwrap_or(::std::f64::INFINITY);

        let already_in_equivocators = sender_state.equivocators.contains(sender);

        match (is_equivocation, already_in_equivocators) {
            // if it's already equivocating and listed as such,
            // or not equivocating at all, an insertion can be
            // done without more checks
            (false, _) | (true, true) => {
                let success = self.insert(msg.clone());
                if success {
                    sender_state.latest_msgs.update(msg);
                }
                (success, sender_state)
            }
            // in the other case, we have to check that the threshold is not
            // reached
            (true, false) => {
                if sender_weight + sender_state.state_fault_weight <= sender_state.thr {
                    let success = self.insert(msg.clone());
                    if success {
                        sender_state.latest_msgs.update(msg);
                        if sender_state.equivocators.insert(sender.clone()) {
                            sender_state.state_fault_weight += sender_weight;
                        }
                    }
                    (success, sender_state)
                } else {
                    (false, sender_state)
                }
            }
        }
    }

    /// this function sets the weight of the equivocator to zero right away
    /// (returned on sender::State) and add his message to the state, since now his
    /// equivocation doesnt count to the state fault weight anymore
    pub fn faulty_insert_with_slash(
        &mut self,
        msg: &M,
        mut sender_state: sender::State<M>,
    ) -> (bool, sender::State<M>) {
        let is_equivocation = sender_state.latest_msgs.equivocate(msg);
        if is_equivocation {
            let sender = msg.sender();
            sender_state.equivocators.insert(sender.clone());
            sender_state
                .senders_weights
                .insert(sender.clone(), WeightUnit::ZERO);
        }
        sender_state.latest_msgs.update(msg);
        let success = self.insert(msg.clone());
        (success, sender_state)
    }
}

impl<M: message::Trait> Debug for Justification<M> {
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// Set of latest honest messages
pub struct LatestMsgsHonest<M: message::Trait>(HashSet<M>);

impl<M: message::Trait> LatestMsgsHonest<M> {
    /// Create an empty set
    fn new() -> Self {
        LatestMsgsHonest(HashSet::new())
    }

    /// Insert message to the set
    fn insert(&mut self, msg: M) -> bool {
        self.0.insert(msg)
    }

    /// Filters the latest messages
    pub fn from_latest_msgs(
        latest_msgs: &LatestMsgs<M>,
        equivocators: &HashSet<M::Sender>,
    ) -> Self {
        latest_msgs
            .iter()
            .filter_map(|(sender, msgs)| {
                if equivocators.contains(sender) || msgs.len() != 1 {
                    None
                } else {
                    msgs.iter().next()
                }
            })
            .fold(LatestMsgsHonest::new(), |mut acc, msg| {
                acc.insert(msg.clone());
                acc
            })
    }

    pub fn iter(&self) -> std::collections::hash_set::Iter<M> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn mk_estimate(
        &self,
        senders_weights: &SendersWeight<<M as message::Trait>::Sender>,
    ) -> Result<M::Estimate, &'static str> {
        M::Estimate::mk_estimate(&self, senders_weights)
    }
}

/// Mapping between senders and their latests messages
/// Latest messages from a sender are all their messages that are not
/// in the dependency of another of their messages
#[derive(Eq, PartialEq, Clone, Default, Debug)]
pub struct LatestMsgs<M: message::Trait>(HashMap<<M as message::Trait>::Sender, HashSet<M>>);

impl<M: message::Trait> LatestMsgs<M> {
    /// Create an empty map
    pub fn new() -> Self {
        LatestMsgs(HashMap::new())
    }

    /// insert a new set of messages for a sender
    pub fn insert(&mut self, k: M::Sender, v: HashSet<M>) -> Option<HashSet<M>> {
        self.0.insert(k, v)
    }

    /// checks whether a sender is already contained in the map
    pub fn contains_key(&self, k: &M::Sender) -> bool {
        self.0.contains_key(k)
    }

    /// get a set of messages sent by the sender
    pub fn get(&self, k: &M::Sender) -> Option<&HashSet<M>> {
        self.0.get(k)
    }

    /// get a set of messages sent by the sender as mut
    pub fn get_mut(&mut self, k: &M::Sender) -> Option<&mut HashSet<M>> {
        self.0.get_mut(k)
    }

    pub fn iter(&self) -> std::collections::hash_map::Iter<M::Sender, HashSet<M>> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn keys(&self) -> std::collections::hash_map::Keys<M::Sender, HashSet<M>> {
        self.0.keys()
    }

    pub fn values(&self) -> std::collections::hash_map::Values<'_, M::Sender, HashSet<M>> {
        self.0.values()
    }

    /// update the data structure by adding a new message
    /// return true if new_message is a valid latest message,
    /// aka the first message of a sender or a message that is not
    /// in the justification of the existing latest messages
    pub fn update(&mut self, new_msg: &M) -> bool {
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
                        false || acc
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
            // no message found for this sender, so new_msg is the latest
            self.insert(sender.clone(), [new_msg.clone()].iter().cloned().collect());
            true
        }
    }

    /// checks whether msg_new equivocates with latest msgs
    pub(crate) fn equivocate(&self, msg_new: &M) -> bool {
        self.get(msg_new.sender())
            .map(|latest_msgs| latest_msgs.iter().any(|m| m.equivocates(&msg_new)))
            .unwrap_or(false)
    }
}

impl<'z, M: message::Trait> From<&'z Justification<M>> for LatestMsgs<M> {
    /// extract the latest messages from a justification
    fn from(j: &Justification<M>) -> Self {
        let mut latest_msgs: LatestMsgs<M> = LatestMsgs::new();
        let mut queue: VecDeque<M> = j.iter().cloned().collect();
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
// impl<'z, M: message::Trait> From<&'z Justification<M>> for LatestMsgs<M> {
//     fn from(j: &Justification<M>) -> Self {
//         fn recur_func<M: message::Trait>(
//             j: &Justification<M>,
//             latest_msgs: LatestMsgs<M>,
//         ) -> LatestMsgs<M> {
//             j.iter().fold(latest_msgs, |mut acc, m| {
//                 acc.update(m);
//                 recur_func(m.justification(), acc)
//             })
//         }
//         recur_func(j, LatestMsgs::new())
//     }
// }
