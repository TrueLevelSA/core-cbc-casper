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

#![cfg(feature = "integration_test")]
extern crate casper;
extern crate proptest;
extern crate rand;

use std::collections::{HashMap, HashSet};
use std::iter;
use std::iter::FromIterator;

use proptest::prelude::*;

use proptest::strategy::ValueTree;
use proptest::test_runner::Config;
use proptest::test_runner::{RngAlgorithm, TestRng, TestRunner};
use rand::seq::SliceRandom;
use rand::thread_rng;

use casper::blockchain::Block;
use casper::estimator::Estimator;
use casper::justification::{Justification, LatestMsgs, LatestMsgsHonest};
use casper::message::{self, Message};
use casper::util::weight::WeightUnit;
use casper::validator;

use casper::IntegerWrapper;
use casper::ValidatorNameBlockData;
use casper::VoteCount;

mod common;
use common::binary::BoolWrapper;

use std::fs::OpenOptions;
use std::io::Write;

use std::time::Instant;

mod tools;
use tools::ChainData;

/// Creates a message for each validator in the validators_recipients_data vector.
/// Messages are added to theirs validators state.
fn create_messages<E, U>(
    state: &mut HashMap<u32, validator::State<E, U>>,
    validators_recipients_data: Vec<(u32, HashSet<u32>)>,
) -> Vec<(Message<E>, u32, HashSet<u32>)>
where
    E: Estimator<ValidatorName = u32>,
    U: WeightUnit,
{
    validators_recipients_data
        // into_iter because we dont want to clone data at the end
        .into_iter()
        .map(|(validator, recipients)| {
            // get all latest messages
            let latest: HashSet<Message<E>> = state[&validator]
                .latests_msgs()
                .iter()
                .fold(HashSet::new(), |acc, (_, lms)| {
                    acc.union(&lms).cloned().collect()
                });

            // remove all messages from latest that are contained in this validator's latest
            // messages justification
            let latest_delta = match state[&validator].latests_msgs().get(&validator) {
                Some(msgs) => match msgs.len() {
                    1 => {
                        let m = msgs.iter().next().unwrap();
                        latest
                            .iter()
                            .filter(|lm| !m.justification().contains(lm))
                            .cloned()
                            .collect()
                    }
                    _ => unimplemented!(),
                },
                None => latest,
            };

            let mut validator_state = state[&validator].clone();
            for m in latest_delta.iter() {
                validator_state.update(&[&m]);
            }
            let m = Message::from_validator_state(validator, &validator_state).unwrap();

            state.insert(validator, validator_state);
            state
                .get_mut(&validator)
                .unwrap()
                .latests_msgs_as_mut()
                .update(&m);

            (m, validator, recipients)
        })
        .collect()
}

/// Sends messages to the recipients they're meant to be sent to.
/// States of the recipients are updated accordingly.
fn add_messages<E>(
    state: &mut HashMap<u32, validator::State<E, f64>>,
    messages_validators_recipients_data: Vec<(Message<E>, u32, HashSet<u32>)>,
) -> Result<(), &'static str>
where
    E: Estimator<ValidatorName = u32>,
{
    messages_validators_recipients_data
        .into_iter()
        .map(|(m, validator, recipients)| {
            recipients
                .into_iter()
                .map(|recipient| {
                    let mut validator_state_reconstructed = validator::State::new(
                        state[&recipient].validators_weights().clone(),
                        0.0,
                        LatestMsgs::from(m.justification()),
                        0.0,
                        HashSet::new(),
                    );

                    for justification_message in m.justification().iter() {
                        validator_state_reconstructed.update(&[&justification_message]);
                    }

                    if m.estimate()
                        != Message::from_validator_state(validator, &validator_state_reconstructed)
                            .unwrap()
                            .estimate()
                    {
                        return Err("Recipient must be able to reproduce the estimate \
                                    from its justification and the justification only.");
                    }

                    let state_to_update = state.get_mut(&recipient).unwrap().latests_msgs_as_mut();
                    state_to_update.update(&m);
                    m.justification().iter().for_each(|m| {
                        state_to_update.update(m);
                    });

                    Ok(())
                })
                .collect()
        })
        .collect()
}

/// Validator strategy that selects one validator at each step, in a round robin manner.
fn round_robin(val: &mut Vec<u32>) -> BoxedStrategy<HashSet<u32>> {
    let v = val.pop().unwrap();
    val.insert(0, v);
    let mut hashset = HashSet::new();
    hashset.insert(v);
    Just(hashset).boxed()
}

/// Validator strategy that picks one validator in the set at random, in a uniform manner.
fn arbitrary_in_set(val: &mut Vec<u32>) -> BoxedStrategy<HashSet<u32>> {
    prop::collection::hash_set(prop::sample::select(val.clone()), 1).boxed()
}

/// Validator strategy that picks some number of validators in the set at random, in a uniform
/// manner.
fn parallel_arbitrary_in_set(val: &mut Vec<u32>) -> BoxedStrategy<HashSet<u32>> {
    let validators = val.clone();
    prop::sample::select((1..=validators.len()).collect::<Vec<usize>>())
        .prop_flat_map(move |val_count| {
            prop::collection::hash_set(prop::sample::select(validators.to_owned()), val_count)
        })
        .boxed()
}

/// Receiver strategy that picks between 0 and n receivers at random, n being the number of
/// validators.
fn some_receivers(_validator: u32, possible_validators: &[u32], rng: &mut TestRng) -> HashSet<u32> {
    let n = rng.gen_range(0, possible_validators.len());
    let mut receivers = HashSet::new();
    // FIXME: this is constant time, however the number of receivers is not uniform as we always
    // pick from the same vec of validators and put them in a hashset, there are some collisons
    for _ in 0..n {
        receivers.insert(possible_validators.choose(rng).unwrap().clone());
    }

    receivers
}

/// Receiver strategy that picks all the receivers.
fn all_receivers(_sender: u32, possible_validators: &[u32], _rng: &mut TestRng) -> HashSet<u32> {
    HashSet::from_iter(possible_validators.iter().cloned())
}

/// Maps each validator from the validator_strategy to a set of receivers, using the
/// receivers_selector function.
fn create_receiver_strategy(
    validators: &[u32],
    validator_strategy: BoxedStrategy<HashSet<u32>>,
    receivers_selector: fn(u32, &[u32], &mut TestRng) -> HashSet<u32>,
) -> BoxedStrategy<HashMap<u32, HashSet<u32>>> {
    let v = validators.to_owned();
    validator_strategy
        // prop_perturb uses a Rng based on the proptest seed, it can therefore safely be used to
        // create random data as they can be re-obtained
        .prop_perturb(move |validators, mut rng| {
            let mut hashmap: HashMap<u32, HashSet<u32>> = HashMap::new();
            validators.iter().for_each(|validator| {
                let hs = receivers_selector(*validator, &v, &mut rng);
                hashmap.insert(*validator, hs);
            });

            hashmap
        })
        .boxed()
}

type SendersStatesMap<E> = HashMap<u32, validator::State<E, f64>>;

fn message_events<E>(
    state: SendersStatesMap<E>,
    validator_receiver_strategy: BoxedStrategy<HashMap<u32, HashSet<u32>>>,
) -> BoxedStrategy<Result<SendersStatesMap<E>, &'static str>>
where
    E: Estimator<ValidatorName = u32> + 'static,
{
    (validator_receiver_strategy, Just(state))
        .prop_map(|(map_validator_receivers, mut state)| {
            let vec_validators_recipients_data = map_validator_receivers.into_iter().collect();
            let vec_data = create_messages(&mut state, vec_validators_recipients_data);
            match add_messages(&mut state, vec_data) {
                Ok(()) => Ok(state),
                Err(e) => Err(e),
            }
        })
        .boxed()
}

fn full_consensus<E>(
    state: &SendersStatesMap<E>,
    _height_of_oracle: u32,
    _vec_data: &mut Vec<ChainData>,
    _chain_id: u32,
    _received_msgs: &mut HashMap<u32, HashSet<Block<ValidatorNameBlockData<u32>>>>,
) -> bool
where
    E: Estimator<ValidatorName = u32>,
{
    let m: HashSet<_> = state
        .iter()
        .map(|(_validator, validator_state)| {
            LatestMsgsHonest::from_latest_msgs(validator_state.latests_msgs(), &HashSet::new())
                .mk_estimate(validator_state.validators_weights())
                .unwrap()
        })
        .collect();
    m.len() == 1
}

/// Performs safety oracle search and adds information to the data parameter.
/// Info added: consensus_height and longest_chain.
/// Return true if some safety oracle is detected at max_height_of_oracle.
/// The threshold for the safety oracle is set to half of the sum of the validators weights.
fn get_data_from_state(
    validator_state: &validator::State<Block<ValidatorNameBlockData<u32>>, f64>,
    max_height_of_oracle: u32,
    data: &mut ChainData,
) -> bool {
    let latest_msgs_honest =
        LatestMsgsHonest::from_latest_msgs(validator_state.latests_msgs(), &HashSet::new());

    let height_selected_chain =
        tools::get_height_selected_chain(&latest_msgs_honest, validator_state);

    let mut consensus_height: i64 = -1;

    let safety_threshold = (validator_state.validators_weights().sum_all_weights()) / 2.0;

    let mut genesis_blocks = HashSet::new();
    genesis_blocks.insert(Block::new(None, ValidatorNameBlockData::new(0)));

    for height in 0..=max_height_of_oracle {
        let is_local_consensus_satisfied = genesis_blocks.iter().cloned().any(|genesis_block| {
            // returns set of btreeset? basically the cliques; if
            // the set is not empty, there is at least one clique
            Block::safety_oracles(
                genesis_block,
                &latest_msgs_honest,
                &HashSet::new(),
                safety_threshold,
                validator_state.validators_weights(),
            ) != HashSet::new()
        });

        consensus_height = if is_local_consensus_satisfied {
            i64::from(height)
        } else {
            break;
        };

        genesis_blocks = tools::get_children_of_blocks(&latest_msgs_honest, genesis_blocks);
        // cant have a consensus over children if there is none
        if genesis_blocks.is_empty() {
            break;
        }
    }
    let is_consensus_satisfied = consensus_height >= i64::from(max_height_of_oracle);

    data.consensus_height = consensus_height;
    data.longest_chain = height_selected_chain;
    is_consensus_satisfied
}

/// Returns true if at least a safety oracle for a block at height_of_oracle
/// adds a new data to vec_data for each new message that is sent.
/// Uses received_msgs to take note of which validator received which messages
fn safety_oracle_at_height(
    state: &HashMap<u32, validator::State<Block<ValidatorNameBlockData<u32>>, f64>>,
    height_of_oracle: u32,
    vec_data: &mut Vec<ChainData>,
    chain_id: u32,
    received_msgs: &mut HashMap<u32, HashSet<Block<ValidatorNameBlockData<u32>>>>,
) -> bool {
    state.iter().for_each(|(id, validator_state)| {
        for (_, msgs) in validator_state.latests_msgs().iter() {
            for msg in msgs.iter() {
                received_msgs.get_mut(id).unwrap().insert(Block::from(msg));
            }
        }
    });
    state.iter().any(|(validator_id, validator_state)| {
        let mut data = ChainData::new(chain_id, state.len() as u32, *validator_id, 0, 0, 0);
        let is_consensus_satisfied =
            get_data_from_state(validator_state, height_of_oracle, &mut data);
        data.nb_messages = received_msgs.get(validator_id).unwrap().len();
        vec_data.push(data);
        is_consensus_satisfied
    })
}

fn clique_collection(
    state: HashMap<u32, validator::State<Block<ValidatorNameBlockData<u32>>, f64>>,
) -> Vec<Vec<Vec<u32>>> {
    state
        .iter()
        .map(|(_, validator_state)| {
            let genesis_block = Block::new(None, ValidatorNameBlockData::new(0));
            let latest_honest_msgs =
                LatestMsgsHonest::from_latest_msgs(validator_state.latests_msgs(), &HashSet::new());
            let safety_oracles = Block::safety_oracles(
                genesis_block,
                &latest_honest_msgs,
                &HashSet::new(),
                // cliques, not safety oracles, because our threshold is 0
                0.0,
                validator_state.validators_weights(),
            );
            safety_oracles
                .into_iter()
                .map(|btree| Vec::from_iter(btree.into_iter()))
                .collect()
        })
        .collect()
}

type ValidatorStatesMap<E> = HashMap<u32, validator::State<E, f64>>;

fn chain<E: 'static, F: 'static, H: 'static>(
    consensus_value_strategy: BoxedStrategy<E>,
    validator_max_count: usize,
    message_producer_strategy: F,
    message_receiver_strategy: fn(u32, &[u32], &mut TestRng) -> HashSet<u32>,
    consensus_satisfied: H,
    consensus_satisfied_value: u32,
    chain_id: u32,
) -> BoxedStrategy<Vec<Result<ValidatorStatesMap<E>, &'static str>>>
where
    E: Estimator<ValidatorName = u32>,
    F: Fn(&mut Vec<u32>) -> BoxedStrategy<HashSet<u32>>,
    H: Fn(
        &HashMap<u32, validator::State<E, f64>>,
        u32,
        &mut Vec<ChainData>,
        u32,
        &mut HashMap<u32, HashSet<Block<ValidatorNameBlockData<u32>>>>,
    ) -> bool,
{
    (
        prop::sample::select((1..validator_max_count).collect::<Vec<usize>>()),
        any::<[u8; 32]>(),
    )
        .prop_flat_map(move |(validators, seed)| {
            (
                prop::collection::vec(consensus_value_strategy.clone(), validators),
                Just(seed),
            )
        })
        .prop_map(move |(votes, seed)| {
            let mut validators: Vec<u32> = (0..votes.len() as u32).collect();
            let mut received_msgs = validators.iter().map(|v| (*v, HashSet::new())).collect();

            let weights: Vec<f64> = iter::repeat(1.0).take(votes.len() as usize).collect();

            let validators_weights =
                validator::Weights::new(validators.iter().cloned().zip(weights).collect());

            let mut state = Ok(validators
                .iter()
                .map(|validator| {
                    let mut justification = Justification::empty();
                    let message = Message::new(
                        *validator,
                        justification.clone(),
                        votes[*validator as usize].clone(),
                    );
                    justification.insert(message);
                    (
                        *validator,
                        validator::State::new(
                            validators_weights.clone(),
                            0.0,
                            LatestMsgs::from(&justification),
                            0.0,
                            HashSet::new(),
                        ),
                    )
                })
                .collect());

            let mut runner = TestRunner::new_with_rng(
                ProptestConfig::default(),
                TestRng::from_seed(RngAlgorithm::ChaCha, &seed),
            );

            let chain = iter::repeat_with(|| {
                let validator_strategy = message_producer_strategy(&mut validators);
                let receiver_strategy = create_receiver_strategy(
                    &validators,
                    validator_strategy,
                    message_receiver_strategy,
                );

                match state.clone() {
                    Ok(st) => {
                        state = message_events(st, receiver_strategy)
                            .new_tree(&mut runner)
                            .unwrap()
                            .current();
                        state.clone()
                    }
                    Err(e) => Err(e),
                }
            });
            // both variable exist to retain the last unlazified result in the chain
            let mut have_consensus = false;
            let mut no_err = true;

            let mut start = Instant::now();
            let mut timestamp_file = OpenOptions::new()
                .create(true)
                .truncate(true)
                .write(true)
                .open("timestamp.log")
                .unwrap();

            let mut stats_file = OpenOptions::new()
                .create(true)
                .truncate(true)
                .write(true)
                .open(format!("stats{:03}.log", chain_id))
                .unwrap();

            let mut vec_data = vec![];

            writeln!(timestamp_file, "start").unwrap();
            let v = Vec::from_iter(chain.take_while(|state| {
                writeln!(timestamp_file, "{:?}", start.elapsed().subsec_micros()).unwrap();

                start = Instant::now();
                match (state, no_err) {
                    (Ok(st), true) => {
                        if have_consensus {
                            false
                        } else {
                            if consensus_satisfied(
                                st,
                                consensus_satisfied_value,
                                &mut vec_data,
                                chain_id,
                                &mut received_msgs,
                            ) {
                                have_consensus = true
                            }
                            true
                        }
                    }
                    (Err(_), true) => {
                        no_err = false;
                        true
                    }
                    (_, false) => false,
                }
            }));

            for chain_data in vec_data {
                writeln!(stats_file, "{}", chain_data).unwrap();
            }

            v
        })
        .boxed()
}

fn arbitrary_blockchain() -> BoxedStrategy<Block<ValidatorNameBlockData<u32>>> {
    let genesis_block = Block::new(None, ValidatorNameBlockData::new(0));
    Just(genesis_block).boxed()
}

#[test]
fn blockchain() {
    let mut config = Config::with_cases(1);
    config.source_file = Some("tests/generative_tests.rs");

    for chain_id in 0..10 {
        // TestRunners run only N times when using Config::with_cases(N);
        // so we have to create a new runner with said config each time we want
        // to simulate a new blockchain.
        // We could increase N but chain_id would be the same for each run and overwrite
        // the blockhain_test_n.log
        // As of 0.9.2, it is not possible to get the current run index for a runner in order
        // to replace the chain_id with something more elegant.
        let mut runner = TestRunner::new(config.clone());

        // truncate if the file already exists
        let output_file = OpenOptions::new()
            .create(true)
            .truncate(true)
            .write(true)
            .open(format!("blockchain_test_{}.log", chain_id))
            .unwrap();
        // close file handle with truncate option
        drop(output_file);

        runner
            .run(
                &chain(
                    arbitrary_blockchain(),
                    6,
                    arbitrary_in_set,
                    all_receivers,
                    safety_oracle_at_height,
                    4,
                    chain_id,
                ),
                |chain| {
                    chain.iter().for_each(|state| {
                        let state = state.as_ref().unwrap();
                        let mut output_file = OpenOptions::new()
                            .create(true)
                            .append(true)
                            .write(true)
                            .open(format!("blockchain_test_{}.log", chain_id))
                            .unwrap();
                        writeln!(
                            output_file,
                            "{{lms: {:?},",
                            state
                                .iter()
                                .map(|(_, validator_state)| validator_state.latests_msgs())
                                .collect::<Vec<_>>()
                        )
                        .unwrap();
                        writeln!(output_file, "validatorcount: {:?},", state.keys().len()).unwrap();
                        writeln!(output_file, "clqs: ").unwrap();
                        writeln!(output_file, "{:?}}},", clique_collection(state.clone())).unwrap();
                    });
                    Ok(())
                },
            )
            .unwrap();
    }
}

proptest! {
    #![proptest_config(Config::with_cases(30))]
    #[test]
    fn round_robin_vote_count(
        ref chain in chain(
            VoteCount::arbitrary(),
            5,
            round_robin,
            all_receivers,
            full_consensus,
            0,
            0,
        ),
    ) {
        assert_eq!(
            chain.last().unwrap().as_ref().unwrap_or(&HashMap::new()).keys().len(),
            chain.len(),
            "round robin with n validators should converge in n messages",
        );
    }
}

fn boolwrapper_gen() -> BoxedStrategy<BoolWrapper> {
    any::<bool>().prop_map(BoolWrapper::new).boxed()
}

fn integerwrapper_gen() -> BoxedStrategy<IntegerWrapper> {
    any::<u32>().prop_map(IntegerWrapper::new).boxed()
}

proptest! {
    #![proptest_config(Config::with_cases(30))]
    #[test]
    fn round_robin_binary(
        ref chain in chain(
            boolwrapper_gen(),
            15,
            round_robin,
            all_receivers,
            full_consensus,
            0,
            0,
        ),
    ) {
        assert!(
            chain.last().unwrap().as_ref().unwrap_or(&HashMap::new()).keys().len() >= chain.len(),
            "round robin with n validators should converge in at most n messages",
        );
    }
}

proptest! {
    #![proptest_config(Config::with_cases(10))]
    #[test]
    fn round_robin_integer(
        ref chain in chain(
            integerwrapper_gen(),
            2000,
            round_robin,
            all_receivers,
            full_consensus,
            0,
            0,
        )
    ) {
        // total messages until unilateral consensus
        println!(
            "{} validators -> {:?} message(s)",
            match chain
                .last()
                .unwrap()
                .as_ref()
                .unwrap_or(&HashMap::new())
                .keys()
                .len()
                .to_string()
                .as_ref()
            {
                "0" => "Unknown",
                x => x,
            },
            chain.len(),
        );
        assert!(
            chain.last().unwrap().as_ref().unwrap_or(&HashMap::new()).keys().len() >= chain.len(),
            "round robin with n validators should converge in at most n messages",
        );
    }
}

proptest! {
    #![proptest_config(Config::with_cases(1))]
    #[test]
    fn arbitrary_messenger_vote_count(
        ref chain in chain(
            VoteCount::arbitrary(),
            8,
            arbitrary_in_set,
            some_receivers,
            full_consensus,
            0,
            0,
        ),
    ) {
        // total messages until unilateral consensus
        println!(
            "{} validators -> {:?} message(s)",
            match chain
                .last()
                .unwrap()
                .as_ref()
                .unwrap_or(&HashMap::new())
                .keys()
                .len()
                .to_string()
                .as_ref()
            {
                "0" => "Unknown",
                x => x,
            },
            chain.len(),
        );
    }
}

proptest! {
    #![proptest_config(Config::with_cases(1))]
    #[test]
    fn parallel_arbitrary_messenger_vote_count(
        ref chain in chain(
            VoteCount::arbitrary(),
            8,
            parallel_arbitrary_in_set,
            some_receivers,
            full_consensus,
            0,
            0,
        ),
    ) {
        // total messages until unilateral consensus
        println!(
            "{} validators -> {:?} message(s)",
            match chain
                .last()
                .unwrap()
                .as_ref()
                .unwrap_or(&HashMap::new())
                .keys()
                .len()
                .to_string()
                .as_ref()
            {
                "0" => "Unknown",
                x => x,
            },
            chain.len(),
        );
    }
}

proptest! {
    #![proptest_config(Config::with_cases(1))]
    #[test]
    fn arbitrary_messenger_binary(
        ref chain in chain(
            boolwrapper_gen(),
            100,
            arbitrary_in_set,
            some_receivers,
            full_consensus,
            0,
            0,
        ),
    ) {
        // total messages until unilateral consensus
        println!(
            "{} validators -> {:?} message(s)",
            match chain
                .last()
                .unwrap()
                .as_ref()
                .unwrap_or(&HashMap::new())
                .keys()
                .len()
                .to_string()
                .as_ref()
            {
                "0" => "Unknown",
                 x => x,
            },
            chain.len(),
        );
    }
}

proptest! {
    #![proptest_config(Config::with_cases(1))]
    #[test]
    fn arbitrary_messenger_integer(
        ref chain in chain(
            integerwrapper_gen(),
            50,
            arbitrary_in_set,
            some_receivers,
            full_consensus,
            0,
            0,
        ),
    ) {
        // total messages until unilateral consensus
        println!(
            "{} validators -> {:?} message(s)",
            match chain
                .last()
                .unwrap()
                .as_ref()
                .unwrap_or(&HashMap::new())
                .keys()
                .len()
                .to_string()
                .as_ref()
            {
                "0" => "Unknown",
                x => x,
            },
            chain.len(),
        );
    }
}

prop_compose! {
    fn votes(validators: usize, equivocations: usize)
        (
            votes in prop::collection::vec(prop::bool::weighted(0.3), validators as usize),
            equivocations in Just(equivocations),
            validators in Just(validators),
        )
        -> (Vec<Message<VoteCount>>, HashSet<u32>, usize)
    {
        let mut validators_enumeration: Vec<u32> = (0..validators as u32).collect();
        validators_enumeration.shuffle(&mut thread_rng());
        let equivocators: HashSet<u32> = validators_enumeration
            .into_iter()
            .take(equivocations)
            .collect();

        let mut messages = vec![];
        votes
            .iter()
            .enumerate()
            .for_each(|(validator, vote)| {
                messages.push(VoteCount::create_vote_msg(validator as u32, *vote))
            });
        equivocators
            .iter()
            .for_each(|equivocator| {
                let vote = !votes[*equivocator as usize];
                messages.push(VoteCount::create_vote_msg(*equivocator as u32, vote))
            });
        (messages, equivocators, validators)
    }
}

proptest! {
    #![proptest_config(Config::with_cases(1000))]
    #[test]
    fn detect_equivocation_one_equivocation(ref vote_tuple in votes(5, 5)) {
        let (messages, _, nodes) = vote_tuple;
        let nodes = *nodes;

        let validators_weights = validator::Weights::new(
            (0..nodes as u32).zip(iter::repeat(1.0)).collect(),
        );
        let mut validator_state = validator::State::new(
            validators_weights,
            0.0,
            LatestMsgs::empty(),
            0.0,
            HashSet::new(),
        );

        // here, only take one equivocation
        let single_equivocation: Vec<_> =
            messages[..=nodes]
                .iter()
                .map(|message| message)
                .collect();
        let equivocator = messages[nodes].sender();
        for m in single_equivocation.iter() {
            validator_state.update(&[&m]);
        }
        let m0 =
            &Message::from_validator_state(0, &validator_state)
            .unwrap();
        let equivocations: Vec<_> =
            single_equivocation
                .iter()
                .filter(|message| message.equivocates(&m0))
                .collect();
        assert!(
            if *equivocator == 0 {equivocations.len() == 2} else {equivocations.is_empty()},
            "should detect both validator 0 equivocating messages if validator 0 equivocates",
        );
    }
}

proptest! {
    #![proptest_config(Config::with_cases(1000))]
    #[test]
    fn detect_equivocation_all_equivocate(ref vote_tuple in votes(5, 5)) {
        let (messages, _, nodes) = vote_tuple;
        let nodes = *nodes;

        let validators_weights = validator::Weights::new(
            (0..nodes as u32).zip(iter::repeat(1.0)).collect(),
        );
        let mut validator_state = validator::State::new(
            validators_weights,
            0.0,
            LatestMsgs::empty(),
            0.0,
            HashSet::new(),
        );

        for message in messages.iter() {
            validator_state.update(&[&message]);
        }
        let result = &Message::from_validator_state(0, &validator_state);
        match result {
            Err(message::Error::NoNewMessage) => (),
            _ => panic!(
                "from_validator_state should return NoNewMessage when \
                state.latest_msgs contains only equivocating messages"
            ),
        };
        assert!(
            validator_state.equivocators().is_empty(),
            "when state.thr is 0, state.equivocators should be empty",
        );
    }
}

proptest! {
    #![proptest_config(Config::with_cases(1000))]
    #[test]
    fn detect_equivocation_all_equivocate_high_thr(ref vote_tuple in votes(5, 5)) {
        let (messages, equivocators, nodes) = vote_tuple;
        let nodes = *nodes;

        let validators_weights = validator::Weights::new(
            (0..nodes as u32).zip(iter::repeat(1.0)).collect(),
        );
        let mut validator_state = validator::State::new(
            validators_weights,
            0.0,
            LatestMsgs::empty(),
            equivocators.len() as f64,
            HashSet::new(),
        );
        for message in messages.iter() {
            validator_state.update(&[&message]);
        }
        let result = &Message::from_validator_state(0, &validator_state);
        match result {
            Err(message::Error::NoNewMessage) => (),
            _ => panic!(
                "from_validator_state should return NoNewMessage when \
                state.latest_msgs contains only equivocating messages"
            ),
        };
        assert_eq!(
            validator_state.equivocators().len(),
            equivocators.len(),
            "when state.thr is arbitrarily big, state.equivocators should be filled with every \
             equivocator",
        );
    }
}

prop_compose! {
    /// `latest_msgs` produces a `LatestMsgs<VoteCount>` and a `HashSet<u32>`
    /// (equivocators). To produce that we create a `validator::State` and a
    /// `Justification` and use `Justification::from_msg` to populate the
    /// `latest_msgs` and `equivocators` field in the state, which we then
    /// return here.
    fn latest_msgs(validators_count: usize)
        (
            equivocations in prop::collection::vec(
                0..validators_count,
                0..validators_count,
            ),
            votes in prop::collection::vec(
                VoteCount::arbitrary(),
                validators_count,
            ),
            validators_count in Just(validators_count),
        )
        -> (LatestMsgs<VoteCount>, HashSet<u32>)
    {
        let latest_msgs = LatestMsgs::empty();
        let equivocators = HashSet::new();

        let validators_weights = validator::Weights::new(
            (0..validators_count)
                .map(|s| s as u32)
                .zip(std::iter::repeat(1.0))
                .collect(),
        );

        let mut validator_state = validator::State::new(
            validators_weights,
            0.0,
            latest_msgs,
            4.0,
            equivocators,
        );

        let mut messages = vec![];
        for (validator, vote) in votes.iter().enumerate().take(validators_count) {
            messages.push(Message::new(validator as u32, Justification::empty(), *vote));

            if equivocations.contains(&validator) {
                messages.push(Message::new(
                    validator as u32,
                    Justification::empty(),
                    vote.toggled_vote(),
                ));
            }
        }

        Justification::from_msgs(messages, &mut validator_state);

        (validator_state.latests_msgs().clone(), validator_state.equivocators().clone())
    }
}

proptest! {
    #[test]
    fn latest_msgs_honest_from_latest_msgs((latest_msgs, equivocators) in latest_msgs(10)) {
        let latest_msgs_honest = LatestMsgsHonest::from_latest_msgs(&latest_msgs, &equivocators);
        assert!(
            !latest_msgs_honest
                .iter()
                .any(|msg| equivocators.contains(&msg.sender()))
        );
        assert_eq!(
            latest_msgs_honest.len(),
            latest_msgs.len() - equivocators.len(),
            "Latest honest messages length should be the same as latest messages minus equivocators"
        );
    }
}
