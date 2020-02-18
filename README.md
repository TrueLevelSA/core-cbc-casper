[![pipeline status](https://gitlab.com/TrueLevel/casper/core-cbc/badges/master/pipeline.svg)](https://gitlab.com/TrueLevel/casper/core-cbc/commits/master) [![License: AGPL v3](https://img.shields.io/badge/License-AGPL%20v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)

Core CBC Casper
===

Abstract message library for CBC Casper, written in Rust.

**DISCLAIMER:** This library is experimental, under development, not reviewed,
and might change dramatically.

The purpose of this library is to abstractly define the CBC Casper, as defined
in [Introducing the "minimal" CBC Casper Consensus
Protocols](https://github.com/cbc-casper/cbc-casper-paper), message stucture and
define functions for the construction and proper execution of protocols of the
casper family. We aimed at pushing as much functionality as possible directly to
the abstract message layer, in such a way that a developer can create a protocol
fairly easy using this library.

The design decision is to be as general as possible, and leave all specifics for
the implementer of the protocol. For the time being, we aim at mathematical
correctness and mostly purely functional protocol executions, rather than on
performance. The idea is to have a mathematically correct and possibly
inefficient implementations of functions that can be used as ground truth for
comparing with efficient implementations.

## Using the library

To benefit from the CBC Casper safety proofs this library builds upon,
the `validator::ValidatorName` and `estimmator::Estimator` traits must be
implemented.

We also present a basic blockchain implementation heavily under developement.
You can also find another implementation of an integer consensus in `tests/`.

But in order to get started using the library, the best way is to study the
examples in the documentation and in the examples folder (under development).
It is also instructive to read and run the tests.

### Cargo

You can use this library in your dependencies with

```
[dependencies]
core_cbc_casper = "0.1"
```

## Example

We present an example of naive consensus protocol: a ternary consensus that uses
the generic type `message::Message<estimator::Estimator>` implementation to
generate the protocol.

## Known limitations

### Performance

As mentioned earlier, our current focus is on the correctness of the
implementation rather than on performance.

### Error handling

The error handling has had poor focus for now. Potential points of failure must be
properly studied and fixed if necessary before the library can be considered to be
ready for production.

## Tests

We use the crate `proptest` to generate property tests. The library has a
feature `integration_test` used by the proptest framework. To run specifically
the `proptest` tests use:

```
cargo test --test generative_tests --features "integration_test"
```

To run the other tests simply use `cargo test`.

## Benchmarking

We use the crate `criterion` for benchmarking. The library provides statistical
insight into performance regression and improvement, and optionally depends on
`gnuplot` to plot detailed graphs of benchmarks results. To run the benchmark, use:

```
cargo bench
```

### Artefacts
The plots and saved data are stored under `target/criterion/$BENCHMARK_NAME/`.

The `new` folder contains the statistics for the last benchmarking run, while the `base` folder
contains those for the last run on the `base` baseline (see [Command-Line
Options](./command_line_options.md#baselines) for more information on baselines). The plots are in
the `report` folder. Criterion.rs only keeps historical data for the last run. The `report/both`
folder contains plots which show both runs on one plot, while the `report/change` folder contains
plots showing the differences between the last two runs. This example shows the plots produced by
the default `bench_function` benchmark method. Other methods may produce additional charts, which
will be detailed in their respective pages.

For further reading, reference [Plots & Graphs](https://bheisler.github.io/criterion.rs/book/user_guide/plots_and_graphs.html)

## Contributing

At this point the development of this library is only internal. If you want to
contribute please contact one of the authors of the library (see Cargo.toml).

### Code Format

We use `rustfmt` default configuration to ensure a coherent code format in the
entire project. Install `rustfmt` with `rustup component add rustfmt`.

### Code Linting

We use `clippy` to ensure the code base is as clean and functional as possible.
Install it with `rustup component add clippy` and run it with `cargo clippy --all-targets
--all-features -- -D warnings`.

## More on CBC Casper

To read more about CBC Casper:
* [Casper CBC, Simplified!](
https://medium.com/@aditya.asgaonkar/casper-cbc-simplified-2370922f9aa6),
by Aditya Asgaonkar.
