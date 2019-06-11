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

//! ## Validators
//!
//! Validators produce and recieve messages (`message::Trait`) from other validators in the
//! network. When a validator want to produce a message he needs to collect his justification
//! (`Justification`) and run an estimator (`Estimate`) to get a value. See [§ Estimator
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
//! When a node (`sender::Trait`) equivocates, it is basically executing multiple separate
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

use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;

use crate::justification::LatestMsgs;
use crate::message;
use crate::traits::Zero;
use crate::util::weight::{SendersWeight, WeightUnit};

/// All casper actors that send messages, aka validators, have to implement the sender trait
pub trait Trait: Hash + Clone + Ord + Eq + Send + Sync + Debug + serde::Serialize {}

// Default implementations

impl Trait for u8 {}
impl Trait for u32 {}
impl Trait for u64 {}
impl Trait for i8 {}
impl Trait for i32 {}
impl Trait for i64 {}

/// Inner state of a sender. Sender's state implement `message::Trait` allowing senders to produce
/// messages based on their latest view of the network.
#[derive(Debug, Clone)]
pub struct State<M: message::Trait> {
    /// current state total fault weight
    pub(crate) state_fault_weight: WeightUnit,
    /// fault tolerance threshold
    pub(crate) thr: WeightUnit,
    /// current validator set, mapped to their respective weights
    pub(crate) senders_weights: SendersWeight<M::Sender>,
    /// this sender's latest message
    pub(crate) own_latest_msg: Option<M>,
    pub(crate) latest_msgs: LatestMsgs<M>,
    pub(crate) equivocators: HashSet<M::Sender>,
}

impl<M: message::Trait> State<M> {
    pub fn new(
        senders_weights: SendersWeight<M::Sender>,
        state_fault_weight: WeightUnit,
        own_latest_msg: Option<M>,
        latest_msgs: LatestMsgs<M>,
        thr: WeightUnit,
        equivocators: HashSet<M::Sender>,
    ) -> Self {
        State {
            senders_weights,
            equivocators,
            state_fault_weight,
            thr,
            own_latest_msg,
            latest_msgs,
        }
    }

    pub fn from_state(
        sender_state: State<M>,
        senders_weights: Option<SendersWeight<M::Sender>>,
        state_fault_weight: Option<WeightUnit>,
        own_latest_msg: Option<Option<M>>,
        latest_msgs: Option<LatestMsgs<M>>,
        thr: Option<WeightUnit>,
        equivocators: Option<HashSet<M::Sender>>,
    ) -> State<M> {
        State {
            senders_weights: senders_weights.unwrap_or(sender_state.senders_weights),
            state_fault_weight: state_fault_weight.unwrap_or(sender_state.state_fault_weight),
            own_latest_msg: own_latest_msg.unwrap_or(sender_state.own_latest_msg),
            latest_msgs: latest_msgs.unwrap_or(sender_state.latest_msgs),
            thr: thr.unwrap_or(sender_state.thr),
            equivocators: equivocators.unwrap_or(sender_state.equivocators),
        }
    }

    pub fn equivocators(&self) -> &HashSet<M::Sender> {
        &self.equivocators
    }

    pub fn senders_weights(&self) -> &SendersWeight<M::Sender> {
        &self.senders_weights
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

    pub fn fault_weight(&self) -> WeightUnit {
        self.state_fault_weight
    }

    /// get msgs and fault weight overhead and equivocators overhead sorted
    /// by fault weight overhead against the current sender_state
    pub fn sort_by_faultweight<'z>(&self, msgs: HashSet<&'z M>) -> Vec<&'z M> {
        let mut msgs_sorted_by_faultw: Vec<_> = msgs
            .iter()
            .filter_map(|&msg| {
                // equivocations in relation to state
                let sender = msg.sender();
                if !self.equivocators.contains(sender) && self.latest_msgs.equivocate(msg) {
                    self.senders_weights.weight(sender).map(|w| (msg, w)).ok()
                } else {
                    Some((msg, WeightUnit::ZERO))
                }
            })
            .collect();

        let _ = msgs_sorted_by_faultw.sort_unstable_by(|(m0, w0), (m1, w1)| {
            w0.partial_cmp(w1).unwrap_or_else(|| m0.getid().cmp(&m1.getid())) // tie breaker
        });

        // return a Vec<message::Trait>
        msgs_sorted_by_faultw
            .iter()
            .map(|(m, _)| m)
            .cloned()
            .collect()
    }
}
