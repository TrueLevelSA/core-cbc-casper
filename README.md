[![pipeline status](https://gitlab.com/TrueLevel/casper/core-cbc/badges/master/pipeline.svg)](https://gitlab.com/TrueLevel/casper/core-cbc/commits/master) [![License: AGPL v3](https://img.shields.io/badge/License-AGPL%20v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)

CBC Casper Abstract Message Library
===

**DISCLAIMER:** This library is experimental, under develepment, not reviewed,
and might change dramatically.

The purpose of this library is to abstractly define the CBC Casper, as defined
in [Introducing the "minimal" CBC Casper Consensus
Protocols](https://github.com/cbc-casper/cbc-casper-paper), message stucture and
define functions for the construction and proper execution of protocols of the
casper family. We aimed at pushing as much functionality as possible directly to
the abstract message layer, in such a way that a developer can create a protocol
fairly easy using this library.

The design decision was to be as general as possible, and leave all the specific
stuff for the implementer of the protocol. For the time being, we aim at
mathematical correctness, and mostly purely functional protocol executions,
rather than on performance. The idea is to have a mathematicaly correct and
possibly ineficient version of functions that can be used as ground truth for
comparing with efficient versions.

## Using the library

To benefit from the CBC Casper safety proofs this library builds upon,
developers have to implement the `message::Trait`. This trait in turn
requires implementing other traits in this library, such as the `Sender` trait
for validators, the `Estimate` trait for the estimate, and the `Data` trait if
the estimate carries data.

One generic type implements the `message::Trait`, namely
`message::Message<Estimate, Sender>`, and can be used to helps getting to a
compliant `message::Trait` concrete type implementation easily.

We also present an basic blockchain implementation heavily under developement
and experiment. You can also find an other implementation of an integer
consensus in `tests/`.

But in order to get started using the library, the best way is to study the
examples folder (under developement). It is also instructive to run the tests.

### Cargo

The library is not yet published on crates.io but you can use it in your
dependencies with

```
[dependencies]
capser = { git = "https://github.com/TrueLevelSA/cbc-casper-msg" }
```

## Example

We present an example of naive consensus protocol: a ternary consensus that uses
the generic type `message::Message<Estimate, Sender>` implementation to generate
the protocol.

## Known limitations

### Performance

As mentionned earlier our current focus is on the correctness of the
implementation rather than on performance.

## Tests

We use the crate `proptest` to generate properties tests. The library has a
feature `integration_test` used by the proptest framework. To run specificaly
the `proptest` tests use:

```
cargo test --test generative_tests --features "integration_test"
```

To run the other tests simply use `cargo test`.

## Contributing

At this point the development of this library is only internal. If you want to
contribute please contact one of the authors of the library (see Cargo.toml).

### Code Format

We use `rustfmt` default configuration to ensure a coherent code format in the
entire project. Install `rustfmt` with `rustup component add rustfmt`.
