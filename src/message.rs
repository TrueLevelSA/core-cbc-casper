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
use serde::Serialize;

use crate::estimator::Estimator;
use crate::justification::{Justification, LatestMsgsHonest};
use crate::util::hash::Hash;
use crate::util::id::Id;
use crate::util::weight::WeightUnit;
use crate::validator;

#[derive(Debug)]
pub enum Error<E: std::error::Error> {
    Estimator(E),
    NoNewMessage,
}

impl<E: std::error::Error> std::fmt::Display for Error<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::Estimator(err) => std::fmt::Display::fmt(&err, f),
            Error::NoNewMessage => writeln!(f, "No message could be added to the state"),
        }
    }
}

impl<E: std::error::Error> std::error::Error for Error<E> {}

// Mathematical definition of a casper message with (value, validator, justification)
#[derive(Clone, Eq, PartialEq)]
struct ProtoMsg<E: Estimator> {
    estimate: E,
    sender: E::ValidatorName,
    justification: Justification<E>,
}

impl<E: Estimator> Id for ProtoMsg<E> {
    type ID = Hash;
}

impl<E: Estimator> Serialize for ProtoMsg<E> {
    fn serialize<T: serde::Serializer>(&self, serializer: T) -> Result<T::Ok, T::Error> {
        use serde::ser::SerializeStruct;

        let mut msg = serializer.serialize_struct("Message", 3)?;
        let j: Vec<_> = self.justification.iter().map(Message::getid).collect();
        msg.serialize_field("sender", &self.sender)?;
        msg.serialize_field("estimate", &self.estimate)?;
        msg.serialize_field("justification", &j)?;
        msg.end()
    }
}

/// Concrete Casper message implementing `message::Trait` containing a value as `Estimator`, a
/// validator as `validator::ValidatorName`, and a justification as `Justification`.
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
/// // Implement Estimator for Value...
///
/// type Validator = u64;
///
/// type Message = message::Message<Value>;
/// ```
///
/// `Value` must implement `Estimator` to be valid for a `message::Message` and to produce
/// estimates.
#[derive(Eq, Clone)]
pub struct Message<E: Estimator>(Arc<ProtoMsg<E>>, Hash);

impl<E: Estimator> Message<E> {
    pub fn sender(&self) -> &E::ValidatorName {
        &self.0.sender
    }

    pub fn estimate(&self) -> &E {
        &self.0.estimate
    }

    pub fn justification<'z>(&'z self) -> &'z Justification<E> {
        &self.0.justification
    }

    pub fn new(sender: E::ValidatorName, justification: Justification<E>, estimate: E) -> Self {
        let proto = ProtoMsg {
            sender,
            justification,
            estimate,
        };
        // Message is not mutable, id is computed only once at creation
        let id = proto.getid();
        Message(Arc::new(proto), id)
    }

    /// Create a message from newly received messages.
    pub fn from_msgs<U: WeightUnit>(
        sender: E::ValidatorName,
        mut new_msgs: Vec<&Self>,
        validator_state: &mut validator::State<E, U>,
    ) -> Result<Self, Error<E::Error>> {
        // dedup by putting msgs into a hashset
        let new_msgs: HashSet<_> = new_msgs.drain(..).collect();
        let new_msgs_len = new_msgs.len();

        // update latest_msgs in validator_state with new_msgs
        let mut justification = Justification::empty();
        let inserted_msgs = justification.faulty_inserts(&new_msgs, validator_state);

        if inserted_msgs.is_empty() && new_msgs_len > 0 {
            Err(Error::NoNewMessage)
        } else {
            let latest_msgs_honest = LatestMsgsHonest::from_latest_msgs(
                validator_state.latests_msgs(),
                validator_state.equivocators(),
            );

            let estimate = latest_msgs_honest.mk_estimate(&validator_state.validators_weights());
            estimate
                .map(|e| Self::new(sender, justification, e))
                .map_err(Error::Estimator)
        }
    }

    // FIXME: insanely expensive to compute
    pub fn equivocates_indirect(
        &self,
        rhs: &Self,
        mut equivocators: HashSet<E::ValidatorName>,
    ) -> (bool, HashSet<E::ValidatorName>) {
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
    pub fn equivocates(&self, rhs: &Self) -> bool {
        self != rhs && self.sender() == rhs.sender() && !rhs.depends(self) && !self.depends(rhs)
    }

    /// Checks whether self depends on rhs or not. Returns true if rhs is somewhere in the
    /// justification of self. This check is heavy and work well only with messages where the
    /// dependency is found on the surface, which what it was designed for.
    pub fn depends(&self, rhs: &Self) -> bool {
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
        fn recurse<E: Estimator>(
            lhs: &Message<E>,
            rhs: &Message<E>,
            visited: Arc<RwLock<HashSet<Message<E>>>>,
        ) -> bool {
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
}

impl<E: Estimator> Id for Message<E> {
    type ID = Hash;

    // Redefine getid to not recompute the hash every time
    fn getid(&self) -> Self::ID {
        self.1
    }
}

impl<E: Estimator> Serialize for Message<E> {
    fn serialize<T: serde::Serializer>(&self, serializer: T) -> Result<T::Ok, T::Error> {
        serde::Serialize::serialize(&self.0, serializer)
    }
}

impl<E: Estimator> std::hash::Hash for Message<E> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.getid().hash(state)
    }
}

impl<E: Estimator> PartialEq for Message<E> {
    fn eq(&self, rhs: &Self) -> bool {
        Arc::ptr_eq(&self.0, &rhs.0) || self.getid() == rhs.getid() // should make this line unnecessary
    }
}

impl<E: Estimator> Debug for Message<E> {
    // Note: format used for rendering illustrative gifs from generative tests; modify with care
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "M{:?}({:?})", self.sender(), self.estimate().clone())
    }
}
