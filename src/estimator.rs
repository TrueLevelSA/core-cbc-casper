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

use std::error::Error;
use std::fmt::Debug;
use std::hash::Hash;

use crate::justification::LatestMessagesHonest;
use crate::util::weight::WeightUnit;
use crate::validator;

/// Describes an estimate, or a value of the consensus at a certain time. Implementing this trait
/// allows to produce an estimate given the set of [`latest messages`] and the set of [`validators`] and
/// their [`weights`].
///
/// [`latest messages`]: ../justification/struct.LatestMessages.html
/// [`validators`]: ../validator/trait.ValidatorName.html
/// [`weights`]: ../validator/struct.Weights.html
///
/// # Example
///
/// This lengthy example showcases how to declare a simple type implementing the Estimator trait.
///
/// ```
/// use core_cbc_casper::message::Message;
/// use core_cbc_casper::validator;
/// use core_cbc_casper::justification::{LatestMessagesHonest, LatestMessages, Justification};
/// use core_cbc_casper::estimator::Estimator;
/// use core_cbc_casper::util::weight::WeightUnit;
///
/// use std::collections::HashSet;
///
/// // An error type is needed for the different ways the estimate functions could fail. This
/// // example is too minimalistic for this to be a concern.
/// #[derive(Debug)]
/// pub struct Error();
///
/// impl std::error::Error for Error{};
///
/// impl std::fmt::Display for Error {
///     fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
///         writeln!(f, "Error!")
///     }
/// }
///
/// type Validator = u64;
///
/// // The value type we declare is a trivial boolean wrapper with a single function for the
/// // estimate function.
/// #[derive(Debug, Hash, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, serde_derive::Serialize)]
/// struct Value {
///     boolean: bool,
/// };
///
/// impl Value {
///     fn and(&self, other: &Self) -> Self {
///         Value { boolean: self.boolean && other.boolean }
///     }
/// }
///
/// impl Estimator for Value {
///     type ValidatorName = Validator;
///     type Error = Error;
///
///     // This example's simple estimate function estimates `true` if every input message is
///     // `true`, otherwise the result is `false`.
///     fn estimate<U: WeightUnit>(
///         latest_messages: &LatestMessagesHonest<Value>,
///         validators_weights: &validator::Weights<Validator, U>,
///     ) -> Result<Self, Self::Error> {
///         Ok(latest_messages
///             .iter()
///             .fold(Value { boolean: true }, |acc, message| {
///                 acc.and(message.estimate())
///             })
///         )
///     }
/// }
///
/// let weights = validator::Weights::new(vec![(0, 1.0), (1, 1.0), (2, 1.0)].into_iter().collect());
///
/// let mut latest_messages = LatestMessages::empty();
/// latest_messages.update(&Message::new(0, Justification::empty(), Value { boolean: true }));
/// latest_messages.update(&Message::new(1, Justification::empty(), Value { boolean: true }));
///
/// assert!(
///     Value::estimate(
///         &LatestMessagesHonest::from_latest_messages(
///             &latest_messages,
///             &HashSet::new(),
///         ),
///         &weights,
///     ).unwrap().boolean
/// );
///
/// latest_messages.update(&Message::new(2, Justification::empty(), Value { boolean: false }));
///
/// assert!(
///     !Value::estimate(
///         &LatestMessagesHonest::from_latest_messages(
///             &latest_messages,
///             &HashSet::new(),
///         ),
///         &weights,
///     ).unwrap().boolean
/// );
/// ```
pub trait Estimator: Hash + Eq + Clone + Send + Sync + Debug + serde::Serialize {
    type ValidatorName: validator::ValidatorName;
    type Error: Error;

    /// Chooses an estimate from a set of latest messages.
    fn estimate<U: WeightUnit>(
        latest_messages: &LatestMessagesHonest<Self>,
        validators_weights: &validator::Weights<Self::ValidatorName, U>,
    ) -> Result<Self, Self::Error>;
}
