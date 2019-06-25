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

//! CBC Casper Abstract Message Library
//! ===
//!
//! **DISCLAIMER:** This library is experimental, under development, not reviewed, and might change
//! dramatically.
//!
//! The purpose of this library is to abstractly define the CBC Casper, as defined in [Introducing
//! the "minimal" CBC Casper Consensus Protocols](https://github.com/cbc-casper/cbc-casper-paper),
//! message stucture and define functions for the construction and proper execution of protocols of
//! the casper family. We aimed at pushing as much functionality as possible directly to the
//! abstract message layer, in such a way that a developer can create a protocol fairly easy using
//! this library.
//!
//! The design decision is to be as general as possible, and leave all specifics for the
//! implementer of the protocol. For the time being, we aim at mathematical correctness and mostly
//! purely functional protocol executions, rather than on performance. The idea is to have a
//! mathematically correct and possibly inefficient implementations of functions that can be used
//! as ground truth for comparing with efficient implementations.
//!
//! ## Using the library
//!
//! To benefit from the CBC Casper safety proofs this library builds upon, developers have to
//! implement `message::Trait`. This trait in turn requires implementing other traits in this
//! library, such as the `sender::Trait` for validators, and the `Estimate` trait for the estimate.
//!
//! One generic type implements the `message::Trait`, namely `message::Message<Estimate,
//! sender::Trait>`, and can be used to helps getting to a compliant `message::Trait` concrete type
//! implementation easily.
//!
//! We also present a basic blockchain implementation heavily under developement.  You can also
//! find another implementation of an integer consensus in `tests/`.
//!
//! But in order to get started using the library, the best way is to study the examples folder
//! (under development). It is also instructive to run the tests.
//!
//! ### Cargo
//!
//! The library is not yet published on crates.io but you can use it in your dependencies with
//!
//! ```text
//! [dependencies]
//! casper = { git = "https://github.com/TrueLevelSA/cbc-casper-msg" }
//!```
//!
//! ## Example
//!
//! We present an example of naive consensus protocol: a ternary consensus that uses the generic
//! type `message::Message<Estimate, sender::Trait>` implementation to generate the protocol.
//!
//! ## Known limitations
//!
//! ### Performance
//!
//! As mentioned earlier, our current focus is on the correctness of the implementation rather than
//! on performance.
//!
//! ## Tests
//!
//! We use the crate `proptest` to generate properties tests. The library has a feature
//! `integration_test` used by the proptest framework. To run specifically the `proptest` tests
//! use:
//!
//! ```text
//! cargo test --test generative_tests --features "integration_test"
//! ```
//!
//! To run the other tests simply use `cargo test`.
//!
//! ## Contributing
//!
//! At this point the development of this library is only internal. If you want to contribute
//! please contact one of the authors of the library (see Cargo.toml).
//!
//! ### Code Format
//!
//! We use `rustfmt` default configuration to ensure a coherent code format in the entire project.
//! Install `rustfmt` with `rustup component add rustfmt`.

extern crate digest;
#[cfg(feature = "integration_test")]
extern crate proptest;
#[cfg(feature = "integration_test")]
extern crate rand;
extern crate rayon;

extern crate bincode;
extern crate blake2;
extern crate itertools;
extern crate serde;
extern crate serde_derive;

/// Implementation of basic types for a casper based blockchain consensus mechanism.
pub mod blockchain;
pub mod estimator;
/// Justifications are supposed to “justify” the proposed values. Justifications of messages are
/// sets of messages that validators has seen and acknowledged while generating messages.
pub mod justification;
/// Messages are generated and passed around by validators in the effort of trying to reach
/// consensus.
pub mod message;
/// Senders are the consensus forming peers nodes in the network are called validators.
pub mod sender;
/// Utility module for various types and components.
pub mod util;

pub use blockchain::{Block, Message};
pub use justification::Justification;
pub use sender::State;
