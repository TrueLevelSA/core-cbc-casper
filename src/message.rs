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

//! ## Messages
//!
//! Messages are the pieces of information generated and passed around by validators while
//! participating in the consensus forming process. In the Casper CBC consensus mechanism, messages
//! have the following structure:
//!
//! ```text
//! Message structure = (value, validator, justification)
//! ```
//!
//! Let us break down the message structure:
//!
//!  * **Value:** The value is the item that the validator proposes the network to come to
//!               consensus on. These values have to be from the set of consensus values. If we are
//!               building an integer consensus algorithm, then the consensus values will be
//!               integers. If we are building a blockchain consensus algorithm, then these
//!               consensus values will be blocks.
//!  * **Validator:** This is the validator who is generating the message.
//!  * **Justification:** The justification of a message is the set of messages that the validator
//!                       has seen and acknowledged while generating that particular message. The
//!                       justification is supposed to “justify” the proposed value.
//!
//! Source: [Casper CBC, Simplified!](https://medium.com/@aditya.asgaonkar/casper-cbc-simplified-2370922f9aa6),
//! by Aditya Asgaonkar.

use std::collections::HashSet;
use std::fmt::Debug;
use std::sync::{Arc, RwLock};

use rayon::prelude::*;

use crate::justification::{Justification, LatestMsgsHonest};
use crate::sender;
use crate::traits::{Estimate, Id};
use crate::util::hash::Hash;

/// Abstraction of a Casper message, contain a value (`Estimate`) that will be sent over the
/// network by validators (`sender::Trait`) and used as `Justification` for a more recent messages.
pub trait Trait:
    std::hash::Hash + Clone + Eq + Sync + Send + Debug + Id + serde::Serialize
{
    /// Defines the validator type that generated this message
    type Sender: sender::Trait;

    /// Defines the estimate type, or value, contained in that message
    /// The estimate type must be compatible with `message::Trait`
    type Estimate: Estimate<M = Self>;

    /// Returns the validator, or sender, who sent this message
    fn sender(&self) -> &Self::Sender;

    /// Returns the estimate, or value, of this message
    fn estimate(&self) -> &Self::Estimate;

    /// Returns the justification of this message
    fn justification<'z>(&'z self) -> &'z Justification<Self>;

    // TODO(h4sh3d): remove because getid() is already available
    fn id(&self) -> &Self::ID;

    /// creates a new instance of this message
    fn new(
        sender: Self::Sender,
        justification: Justification<Self>,
        estimate: Self::Estimate,
        id: Option<Self::ID>,
    ) -> Self;

    /// Create a message from newly received messages.
    fn from_msgs(
        sender: Self::Sender,
        mut new_msgs: Vec<&Self>,
        sender_state: &sender::State<Self>,
    ) -> Result<(Self, sender::State<Self>), &'static str> {
        // dedup by putting msgs into a hashset
        let new_msgs: HashSet<_> = new_msgs.drain(..).collect();
        let new_msgs_len = new_msgs.len();

        // update latest_msgs in sender_state with new_msgs
        let mut justification = Justification::new();
        let (success, sender_state) = justification.faulty_inserts(new_msgs, &sender_state);

        if !success && new_msgs_len > 0 {
            Err("None of the messages could be added to the state!")
        } else {
            let latest_msgs_honest = LatestMsgsHonest::from_latest_msgs(
                sender_state.latests_msgs(),
                sender_state.equivocators(),
            );

            let estimate = latest_msgs_honest.mk_estimate(&sender_state.senders_weights());
            estimate.map(|e| (Self::new(sender, justification, e, None), sender_state))
        }
    }

    // FIXME: insanely expensive to compute
    fn equivocates_indirect(
        &self,
        rhs: &Self,
        mut equivocators: HashSet<<Self as Trait>::Sender>,
    ) -> (bool, HashSet<<Self as Trait>::Sender>) {
        let is_equivocation = self.equivocates(rhs);
        let init = if is_equivocation {
            equivocators.insert(self.sender().clone());
            (true, equivocators)
        } else {
            (false, equivocators)
        };
        self.justification().iter().fold(
            init,
            |(acc_has_equivocations, acc_equivocators), self_prime| {
                // note the rotation between rhs and self, done because descending only on self,
                // thus rhs has to become self on the recursion to get its justification visited
                let (has_equivocation, equivocators) =
                    rhs.equivocates_indirect(self_prime, acc_equivocators.clone());
                let acc_equivocators = acc_equivocators.union(&equivocators).cloned().collect();
                (acc_has_equivocations || has_equivocation, acc_equivocators)
            },
        )
    }

    /// Math definition of the equivocation
    fn equivocates(&self, rhs: &Self) -> bool {
        self != rhs && self.sender() == rhs.sender() && !rhs.depends(self) && !self.depends(rhs)
    }

    /// Checks whether self depends on rhs or not. Returns true if rhs is somewhere in the
    /// justification of self.
    fn depends(&self, rhs: &Self) -> bool {
        // although the recursion ends supposedly only at genesis message, the
        // trick is the following: it short-circuits while descending on the
        // dependency tree, if it finds a dependent message. when dealing with
        // honest validators, this would return true very fast. all the new
        // derived branches of the justification will be evaluated in parallel.
        // say if a msg is justified by 2 other msgs, then the 2 other msgs will
        // be processed on different threads. this applies recursively, so if
        // each of the 2 msgs have say 3 justifications, then each of the 2
        // threads will spawn 3 new threads to process each of the messages.
        // thus, highly parallelizable. when it shortcuts, because in one thread
        // a dependency was found, the function returns true and all the
        // computation on the other threads will be canceled.
        fn recurse<M: Trait>(lhs: &M, rhs: &M, visited: Arc<RwLock<HashSet<M>>>) -> bool {
            let justification = lhs.justification();

            // Math definition of dependency
            justification.contains(rhs)
                || justification
                    .par_iter()
                    .filter(|lhs_prime| {
                        visited
                            .read()
                            .map(|v| !v.contains(lhs_prime))
                            .ok()
                            .unwrap_or(true)
                    })
                    .any(|lhs_prime| {
                        let visited_prime = visited.clone();
                        let _ = visited_prime
                            .write()
                            .map(|mut v| v.insert(lhs_prime.clone()))
                            .ok();
                        recurse(lhs_prime, rhs, visited_prime)
                    })
        }
        let visited = Arc::new(RwLock::new(HashSet::new()));
        recurse(self, rhs, visited)
    }

    /// Checks whether ther is a circular dependency between self and rhs.
    fn is_circular(&self, rhs: &Self) -> bool {
        rhs.depends(self) && self.depends(rhs)
    }
}

// Mathematical definition of a casper message with (value, validator, justification)
#[derive(Clone, Default, Eq, PartialEq)]
struct ProtoMsg<E, S>
where
    E: Estimate<M = Message<E, S>>,
    S: sender::Trait,
{
    estimate: E,
    sender: S,
    justification: Justification<Message<E, S>>,
}

/// Concrete Casper message implementing `message::Trait` containing a value as `Estimate`, a
/// validator as `sender::Trait`, and a justification as `Justification`.
///
/// # Example
///
/// Declare a `Message` type that contains a `Value` as estimate/value, send by validators
/// represented with `u64`.
///
/// ```
/// extern crate casper;
///
/// use casper::message;
///
/// #[derive(Debug, Hash, Clone, Copy, Ord, PartialOrd, Eq, PartialEq)]
/// enum Value {
///     Zero = 0,
///     One = 1,
///     Two = 2,
/// };
///
/// // Implement Estimate for Value...
///
/// type Validator = u64;
///
/// type Message = message::Message<Value, Validator>;
/// ```
///
/// `Value` must implement `Estimate` to be valid for a `message::Message` and to produce
/// estimates.
#[derive(Eq, Clone, Default)]
pub struct Message<E, S>(Arc<ProtoMsg<E, S>>, Hash)
where
    E: Estimate<M = Message<E, S>>,
    S: sender::Trait;

impl<E, S> Id for ProtoMsg<E, S>
where
    E: Estimate<M = Message<E, S>>,
    S: sender::Trait,
{
    type ID = Hash;
}

impl<E, S> Id for Message<E, S>
where
    E: Estimate<M = Self>,
    S: sender::Trait,
{
    type ID = Hash;
    fn getid(&self) -> Self::ID {
        self.1.clone()
    }
}

impl<E, S> serde::Serialize for ProtoMsg<E, S>
where
    E: Estimate<M = Message<E, S>>,
    S: sender::Trait,
{
    fn serialize<T: serde::Serializer>(&self, serializer: T) -> Result<T::Ok, T::Error> {
        use serde::ser::SerializeStruct;

        let mut msg = serializer.serialize_struct("Message", 3)?;
        let j: Vec<_> = self.justification.iter().map(Message::id).collect();
        msg.serialize_field("sender", &self.sender)?;
        msg.serialize_field("estimate", &self.estimate)?;
        msg.serialize_field("justification", &j)?;
        msg.end()
    }
}

impl<E, S> serde::Serialize for Message<E, S>
where
    E: Estimate<M = Self>,
    S: sender::Trait,
{
    fn serialize<T: serde::Serializer>(&self, serializer: T) -> Result<T::Ok, T::Error> {
        use serde::ser::SerializeStruct;
        let mut msg = serializer.serialize_struct("Message", 3)?;
        let j: Vec<_> = self.justification().iter().map(Self::id).collect();
        msg.serialize_field("sender", self.sender())?;
        msg.serialize_field("estimate", self.estimate())?;
        msg.serialize_field("justification", &j)?;
        msg.end()
    }
}

impl<E, S> self::Trait for Message<E, S>
where
    E: Estimate<M = Self>,
    S: sender::Trait,
{
    type Estimate = E;
    type Sender = S;

    fn sender(&self) -> &Self::Sender {
        &self.0.sender
    }

    fn estimate(&self) -> &Self::Estimate {
        &self.0.estimate
    }

    fn justification<'z>(&'z self) -> &'z Justification<Self> {
        &self.0.justification
    }

    fn id(&self) -> &<Self as Id>::ID {
        &self.1
    }

    fn new(
        sender: S,
        justification: Justification<Self>,
        estimate: E,
        id: Option<Self::ID>,
    ) -> Self {
        let proto = ProtoMsg {
            sender,
            justification,
            estimate,
        };
        let id = id.unwrap_or_else(|| proto.getid());
        Message(Arc::new(proto), id)
    }
}

impl<E, S> std::hash::Hash for Message<E, S>
where
    E: Estimate<M = Self>,
    S: sender::Trait,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id().hash(state)
    }
}

impl<E, S> PartialEq for Message<E, S>
where
    E: Estimate<M = Self>,
    S: sender::Trait,
{
    fn eq(&self, rhs: &Self) -> bool {
        Arc::ptr_eq(&self.0, &rhs.0) || self.id() == rhs.id() // should make this line unnecessary
    }
}

impl<E, S> Debug for Message<E, S>
where
    E: Estimate<M = Self>,
    S: sender::Trait,
{
    // Note: format used for rendering illustrative gifs from generative tests; modify with care
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "M{:?}({:?})", self.sender(), self.estimate().clone())
    }
}
