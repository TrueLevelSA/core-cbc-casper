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

use std::collections::{BTreeSet, HashMap, HashSet};
use std::iter;
use std::iter::FromIterator;

use proptest::prelude::*;

use proptest::strategy::ValueTree;
use proptest::test_runner::Config;
use proptest::test_runner::{RngAlgorithm, TestRng, TestRunner};
use rand::seq::SliceRandom;
use rand::thread_rng;

use casper::blockchain::{self, Block};
use casper::estimator::Estimate;
use casper::justification::{Justification, LatestMsgs, LatestMsgsHonest};
use casper::message::{self, Message, Trait};
use casper::sender;
use casper::util::weight::WeightUnit;

mod common;
use common::binary::BoolWrapper;
use common::integer::IntegerWrapper;
use common::vote_count::VoteCount;

use std::fs::OpenOptions;
use std::io::Write;

use std::time::Instant;

mod tools;
use tools::ChainData;

/// create a message for each sender in the senders_recipients_data vector
/// messages are added to theirs senders state
fn create_messages<'z, M, U>(
    state: &'z mut HashMap<M::Sender, sender::State<M, U>>,
    senders_recipients_data: Vec<(M::Sender, HashSet<M::Sender>)>,
) -> Vec<(M, M::Sender, HashSet<M::Sender>)>
where
    M: message::Trait,
    U: WeightUnit,
{
    senders_recipients_data
        // into_iter because we dont want to clone datas at the end
        .into_iter()
        .map(|(sender, recipients)| {
            // get all latest messages
            let latest: HashSet<M> = state[&sender]
                .latests_msgs()
                .iter()
                .fold(HashSet::new(), |acc, (_, lms)| {
                    acc.union(&lms).cloned().collect()
                });

            // remove all messages from latest that are contained in this sender's latest messages
            // justification
            let latest_delta = match state[&sender].latests_msgs().get(&sender) {
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

            let (m, sender_state) = M::from_msgs(
                sender.clone(),
                latest_delta.iter().collect(),
                &state[&sender],
            )
            .unwrap();

            state.insert(sender.clone(), sender_state);
            state
                .get_mut(&sender)
                .unwrap()
                .latests_msgs_as_mut()
                .update(&m);

            (m, sender, recipients)
        })
        .collect()
}

/// send messages to the recipients they're meant to be sent to
/// state of the recipients are updated accordingly
fn add_messages<M>(
    state: &mut HashMap<M::Sender, sender::State<M, f64>>,
    messages_senders_recipients_datas: Vec<(M, M::Sender, HashSet<M::Sender>)>,
) -> Result<(), &'static str>
where
    M: message::Trait,
{
    let result = messages_senders_recipients_datas.into_iter()
        .map(|(m, sender, recipients)|{
        recipients.into_iter().map(|recipient| {

            let sender_state_reconstructed = sender::State::new(
                state[&recipient].senders_weights().clone(),
                0.0,
                Some(m.clone()),
                LatestMsgs::from(m.justification()),
                0.0,
                HashSet::new(),
            );
            if m.estimate()
                != M::from_msgs(
                    sender.clone(),
                    m.justification().iter().collect(),
                    &sender_state_reconstructed,
                )
                .unwrap()
                .0
                .estimate()
            {
                return Err("Recipient must be able to reproduce the estimate from its justification and the justification only.");
            }

            let state_to_update = state.get_mut(&recipient).unwrap().latests_msgs_as_mut();
            state_to_update.update(&m);
            m.justification().iter().for_each(|m| {
                state_to_update.update(m);
            });

            Ok(())

        }).collect()
        }).collect();
    result
}

/// sender strategy that selects one validator at each step, in a round robin manner
fn round_robin(val: &mut Vec<u32>) -> BoxedStrategy<HashSet<u32>> {
    let v = val.pop().unwrap();
    val.insert(0, v);
    let mut hashset = HashSet::new();
    hashset.insert(v);
    Just(hashset).boxed()
}

/// sender strategy that picks one validator in the set at random, in a uniform manner
fn arbitrary_in_set(val: &mut Vec<u32>) -> BoxedStrategy<HashSet<u32>> {
    prop::collection::hash_set(prop::sample::select(val.clone()), 1).boxed()
}

/// sender strategy that picks some number of validators in the set at random, in a uniform manner
fn parallel_arbitrary_in_set(val: &mut Vec<u32>) -> BoxedStrategy<HashSet<u32>> {
    let validators = val.clone();
    prop::sample::select((1..validators.len()).collect::<Vec<usize>>())
        .prop_flat_map(move |val_count| {
            prop::collection::hash_set(prop::sample::select(validators.clone()), val_count)
        })
        .boxed()
}

/// receiver strategy that picks between 0 and n receivers at random, n being the number of validators
fn some_receivers(_sender: &u32, possible_senders: &Vec<u32>, rng: &mut TestRng) -> HashSet<u32> {
    let n = rng.gen_range(0, possible_senders.len());
    let mut receivers: HashSet<u32> = HashSet::new();
    // FIXME: this is constant time, however the number of receivers is not uniform as we always
    // pick from the same vec of senders and put them in a hashset, there are some collisons
    for _ in 0..n {
        receivers.insert(possible_senders.choose(rng).unwrap().clone());
    }

    receivers
}

/// receiver strategy that picks all the receivers
fn all_receivers(_sender: &u32, possible_senders: &Vec<u32>, _rng: &mut TestRng) -> HashSet<u32> {
    HashSet::from_iter(possible_senders.iter().cloned())
}

/// maps each sender from the sender_strategy to a set of receivers, using the receivers_selector
/// function
fn create_receiver_strategy(
    validators: &Vec<u32>,
    sender_strategy: BoxedStrategy<HashSet<u32>>,
    receivers_selector: fn(&u32, &Vec<u32>, &mut TestRng) -> HashSet<u32>,
) -> BoxedStrategy<HashMap<u32, HashSet<u32>>> {
    let v = validators.clone();
    sender_strategy
        // prop_perturb uses a Rng based on the proptest seed, it can therefore safely be used to
        // create random data as they can be re-obtained
        .prop_perturb(move |senders, mut rng| {
            let mut hashmap: HashMap<u32, HashSet<u32>> = HashMap::new();
            senders.iter().for_each(|sender| {
                let hs = receivers_selector(sender, &v, &mut rng);
                hashmap.insert(*sender, hs);
            });

            hashmap
        })
        .boxed()
}

fn message_events<M>(
    state: HashMap<M::Sender, sender::State<M, f64>>,
    sender_receiver_strategy: BoxedStrategy<HashMap<M::Sender, HashSet<M::Sender>>>,
) -> BoxedStrategy<Result<HashMap<M::Sender, sender::State<M, f64>>, &'static str>>
where
    M: 'static + message::Trait,
{
    (sender_receiver_strategy, Just(state))
        .prop_map(|(map_sender_receivers, mut state)| {
            let vec_senders_recipients_datas: Vec<(M::Sender, HashSet<M::Sender>)> =
                map_sender_receivers
                    // into_iter because cloning is unwanted
                    .into_iter()
                    // explicit typing needed for into()
                    .map(|(s, r): (M::Sender, HashSet<M::Sender>)| (s, r))
                    .collect();
            let vec_datas = create_messages(&mut state, vec_senders_recipients_datas);
            let result = add_messages(&mut state, vec_datas);
            match result {
                Ok(()) => Ok(state),
                Err(e) => Err(e),
            }
        })
        .boxed()
}

fn full_consensus<M>(
    state: &HashMap<M::Sender, sender::State<M, f64>>,
    _height_of_oracle: &u32,
    _vec_data: &mut Vec<ChainData>,
    _chain_id: u32,
    _received_msgs: &mut HashMap<u32, HashSet<Block<u32>>>,
) -> bool
where
    M: message::Trait,
{
    let m: HashSet<_> = state
        .iter()
        .map(|(_sender, sender_state)| {
            let latest_honest_msgs =
                LatestMsgsHonest::from_latest_msgs(sender_state.latests_msgs(), &HashSet::new());
            latest_honest_msgs.mk_estimate(sender_state.senders_weights())
        })
        .collect();
    m.len() == 1
}

/// performs safety oracle search and adds information to the data parameter
/// info added: consensus_height and longest_chain
/// return true if some safety oracle is detected at max_heaight_of_oracle
/// the threshold for the safety oracle is set to half of the sum of the senders weights
fn get_data_from_state(
    sender_state: &sender::State<blockchain::Message<u32>, f64>,
    max_height_of_oracle: &u32,
    data: &mut ChainData,
) -> (bool) {
    let latest_msgs_honest =
        LatestMsgsHonest::from_latest_msgs(sender_state.latests_msgs(), &HashSet::new());

    let height_selected_chain = tools::get_height_selected_chain(&latest_msgs_honest, sender_state);

    let mut consensus_height: i64 = -1;

    let safety_threshold = (sender_state.senders_weights().sum_all_weights()) / 2.0;

    let mut genesis_blocks = HashSet::new();
    genesis_blocks.insert(Block::new(None));

    for height in 0..max_height_of_oracle + 1 {
        let truc: Vec<bool> = genesis_blocks
            .iter()
            .cloned()
            .map(|genesis_block| {
                let set_of_stuff = Block::safety_oracles(
                    genesis_block,
                    &latest_msgs_honest,
                    &HashSet::new(),
                    safety_threshold,
                    sender_state.senders_weights(),
                );
                //returns set of btreeset? basically the cliques; if the set is not empty, there is at least one clique
                set_of_stuff != HashSet::new()
            })
            .collect();
        let is_local_consensus_satisfied = truc.contains(&true);

        consensus_height = if is_local_consensus_satisfied {
            height as i64
        } else {
            break;
        };

        genesis_blocks = tools::get_children_of_blocks(&latest_msgs_honest, genesis_blocks);
        // cant have a consensus over children if there is none
        if genesis_blocks.len() == 0 {
            break;
        }
    }
    let is_consensus_satisfied = consensus_height >= *max_height_of_oracle as i64;

    data.consensus_height = consensus_height;
    data.longest_chain = height_selected_chain;
    (is_consensus_satisfied)
}

/// returns true if at least a safety oracle for a block at height_of_oracle
/// adds a new data to vec_data for each new message that is sent
/// uses received_msgs to take note of which validator received which messages
fn safety_oracle_at_height(
    state: &HashMap<u32, sender::State<blockchain::Message<u32>, f64>>,
    height_of_oracle: &u32,
    vec_data: &mut Vec<ChainData>,
    chain_id: u32,
    received_msgs: &mut HashMap<u32, HashSet<Block<u32>>>,
) -> bool {
    state.iter().for_each(|(id, sender_state)| {
        for (_, msgs) in sender_state.latests_msgs().iter() {
            for msg in msgs.iter() {
                received_msgs.get_mut(id).unwrap().insert(Block::from(msg));
            }
        }
    });
    let safety_oracle_detected: HashSet<bool> = state
        .iter()
        .map(|(sender_id, sender_state)| {
            let mut data = ChainData::new(chain_id, state.len() as u32, *sender_id, 0, 0, 0);
            let is_consensus_satisfied =
                get_data_from_state(sender_state, height_of_oracle, &mut data);
            data.nb_messages = received_msgs.get(sender_id).unwrap().len();
            vec_data.push(data);
            is_consensus_satisfied
        })
        .collect();
    safety_oracle_detected.contains(&true)
}

fn clique_collection(
    state: HashMap<u32, sender::State<blockchain::Message<u32>, f64>>,
) -> Vec<Vec<Vec<u32>>> {
    state
        .iter()
        .map(|(_, sender_state)| {
            let genesis_block = Block::new(None);
            let latest_honest_msgs =
                LatestMsgsHonest::from_latest_msgs(sender_state.latests_msgs(), &HashSet::new());
            let safety_oracles = Block::safety_oracles(
                genesis_block,
                &latest_honest_msgs,
                &HashSet::new(),
                // cliques, not safety oracles, because our threshold is 0
                0.0,
                sender_state.senders_weights(),
            );
            let safety_oracles_vec_of_btrees: Vec<BTreeSet<u32>> =
                Vec::from_iter(safety_oracles.iter().cloned());
            let safety_oracles_vec_of_vecs: Vec<Vec<u32>> = safety_oracles_vec_of_btrees
                .iter()
                .map(|btree| Vec::from_iter(btree.iter().cloned()))
                .collect();
            safety_oracles_vec_of_vecs
        })
        .collect()
}

fn chain<E: 'static, F: 'static, H: 'static>(
    consensus_value_strategy: BoxedStrategy<E>,
    validator_max_count: usize,
    message_producer_strategy: F,
    message_receiver_strategy: fn(&u32, &Vec<u32>, &mut TestRng) -> HashSet<u32>,
    consensus_satisfied: H,
    consensus_satisfied_value: u32,
    chain_id: u32,
) -> BoxedStrategy<Vec<Result<HashMap<u32, sender::State<Message<E, u32>, f64>>, &'static str>>>
where
    E: Estimate<M = Message<E, u32>> + From<u32>,
    F: Fn(&mut Vec<u32>) -> BoxedStrategy<HashSet<u32>>,
    //G: Fn(&Vec<u32>, BoxedStrategy<HashSet<u32>>) -> BoxedStrategy<HashMap<u32, HashSet<u32>>>,
    H: Fn(
        &HashMap<u32, sender::State<Message<E, u32>, f64>>,
        &u32,
        &mut Vec<ChainData>,
        u32,
        &mut HashMap<u32, HashSet<Block<u32>>>,
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
            let mut state = HashMap::new();
            let mut validators: Vec<u32> = (0..votes.len() as u32).collect();
            let mut received_msgs: HashMap<u32, HashSet<Block<u32>>> =
                HashMap::from(validators.iter().map(|v| (*v, HashSet::new())).collect());

            let weights: Vec<f64> = iter::repeat(1.0).take(votes.len() as usize).collect();

            let senders_weights = sender::Weights::new(
                validators
                    .iter()
                    .cloned()
                    .zip(weights.iter().cloned())
                    .collect(),
            );

            validators.iter().for_each(|validator| {
                let mut j = Justification::empty();
                let m = Message::new(*validator, j.clone(), votes[*validator as usize].clone());
                j.insert(m.clone());
                state.insert(
                    *validator,
                    sender::State::new(
                        senders_weights.clone(),
                        0.0,
                        Some(m),
                        LatestMsgs::from(&j),
                        0.0,
                        HashSet::new(),
                    ),
                );
            });

            let mut state = Ok(state);
            let mut runner = TestRunner::new_with_rng(
                ProptestConfig::default(),
                TestRng::from_seed(RngAlgorithm::ChaCha, &seed),
            );

            let chain = iter::repeat_with(|| {
                let sender_strategy = message_producer_strategy(&mut validators);
                let receiver_strategy = create_receiver_strategy(
                    &validators,
                    sender_strategy,
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

            let mut vec_data: Vec<ChainData> = vec![];

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
                                &consensus_satisfied_value,
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

fn arbitrary_blockchain() -> BoxedStrategy<Block<u32>> {
    let genesis_block = Block::new(None);
    Just(genesis_block).boxed()
}

#[test]
fn blockchain() {
    let mut config = Config::with_cases(1);
    config.source_file = Some("tests/generative_tests.rs");

    let mut runner = TestRunner::new(config);

    for chain_id in 0..2 {
        runner
            .run(
                &chain(
                    arbitrary_blockchain(),
                    6,
                    arbitrary_in_set,
                    all_receivers,
                    safety_oracle_at_height,
                    4,
                    chain_id + 1, // +1 to match numbering in visualization
                ),
                |chain| {
                    chain.iter().for_each(|state| {
                        let state = state.as_ref().unwrap();
                        let mut output_file = OpenOptions::new()
                            .create(true)
                            .truncate(true)
                            .write(true)
                            .open(format!("blockchain_test_{}.log", chain_id))
                            .unwrap();
                        writeln!(
                            output_file,
                            "{{lms: {:?},",
                            state
                                .iter()
                                .map(|(_, sender_state)| sender_state.latests_msgs())
                                .collect::<Vec<_>>()
                        )
                        .unwrap();
                        writeln!(output_file, "sendercount: {:?},", state.keys().len()).unwrap();
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
    fn round_robin_vote_count(ref chain in chain(VoteCount::arbitrary(), 5, round_robin, all_receivers, full_consensus, 0, 0)) {
        assert_eq!(chain.last().unwrap().as_ref().unwrap_or(&HashMap::new()).keys().len(),
                   if chain.len() > 0 {chain.len()} else {0},
                   "round robin with n validators should converge in n messages")
    }
}

fn boolwrapper_gen() -> BoxedStrategy<BoolWrapper> {
    any::<bool>()
        .prop_map(|boolean| BoolWrapper::new(boolean))
        .boxed()
}

fn integerwrapper_gen() -> BoxedStrategy<IntegerWrapper> {
    any::<u32>()
        .prop_map(|int| IntegerWrapper::new(int))
        .boxed()
}

proptest! {
    #![proptest_config(Config::with_cases(30))]
    #[test]
    fn round_robin_binary(ref chain in chain(boolwrapper_gen(), 15, round_robin, all_receivers, full_consensus, 0, 0)) {
        assert!(chain.last().unwrap().as_ref().unwrap_or(&HashMap::new()).keys().len() >=
                chain.len(),
                "round robin with n validators should converge in at most n messages")
    }
}

proptest! {
    #![proptest_config(Config::with_cases(10))]
    #[test]
    fn round_robin_integer(ref chain in chain(integerwrapper_gen(), 2000, round_robin, all_receivers, full_consensus, 0, 0)) {
        // total messages until unilateral consensus
        println!("{} validators -> {:?} message(s)",
                 match chain.last().unwrap().as_ref().unwrap_or(&HashMap::new()).keys().len().to_string().as_ref()
                 {"0" => "Unknown",
                  x => x},
                 chain.len());
        assert!(chain.last().unwrap().as_ref().unwrap_or(&HashMap::new()).keys().len() >=
                chain.len(),
                "round robin with n validators should converge in at most n messages")
    }
}

proptest! {
    #![proptest_config(Config::with_cases(1))]
    #[test]
    fn arbitrary_messenger_vote_count(ref chain in chain(VoteCount::arbitrary(), 8, arbitrary_in_set, some_receivers, full_consensus, 0, 0)) {
        // total messages until unilateral consensus
        println!("{} validators -> {:?} message(s)",
                 match chain.last().unwrap().as_ref().unwrap_or(&HashMap::new()).keys().len().to_string().as_ref()
                 {"0" => "Unknown",
                  x => x},
                 chain.len());
    }
}

proptest! {
    #![proptest_config(Config::with_cases(1))]
    #[test]
    fn parallel_arbitrary_messenger_vote_count(ref chain in chain(VoteCount::arbitrary(), 8, parallel_arbitrary_in_set, some_receivers, full_consensus, 0, 0)) {
        // total messages until unilateral consensus
        println!("{} validators -> {:?} message(s)",
                 match chain.last().unwrap().as_ref().unwrap_or(&HashMap::new()).keys().len().to_string().as_ref()
                 {"0" => "Unknown",
                  x => x},
                 chain.len());
    }
}

proptest! {
    #![proptest_config(Config::with_cases(1))]
    #[test]
    fn arbitrary_messenger_binary(ref chain in chain(boolwrapper_gen(), 100, arbitrary_in_set, some_receivers, full_consensus, 0, 0)) {
        // total messages until unilateral consensus
        println!("{} validators -> {:?} message(s)",
                 match chain.last().unwrap().as_ref().unwrap_or(&HashMap::new()).keys().len().to_string().as_ref()
                 {"0" => "Unknown",
                  x => x},
                 chain.len());
    }
}

proptest! {
    #![proptest_config(Config::with_cases(1))]
    #[test]
    fn arbitrary_messenger_integer(ref chain in chain(integerwrapper_gen(), 50, arbitrary_in_set, some_receivers, full_consensus, 0, 0)) {
        // total messages until unilateral consensus
        println!("{} validators -> {:?} message(s)",
                 match chain.last().unwrap().as_ref().unwrap_or(&HashMap::new()).keys().len().to_string().as_ref()
                 {"0" => "Unknown",
                  x => x},
                 chain.len());
    }
}

prop_compose! {
    fn votes(senders: usize, equivocations: usize)
        (votes in prop::collection::vec(prop::bool::weighted(0.3), senders as usize),
         equivocations in Just(equivocations),
         senders in Just(senders))
         -> (Vec<Message<VoteCount, u32>>, HashSet<u32>, usize)
    {
        let mut validators: Vec<u32> = (0..senders as u32).collect();
        validators.shuffle(&mut thread_rng());
        let equivocators: HashSet<u32> = HashSet::from_iter(validators[0..equivocations].iter().cloned());

        let mut messages = vec![];
        votes
            .iter()
            .enumerate()
            .for_each(|(sender, vote)|
                      {messages.push(VoteCount::create_vote_msg(sender as u32, vote.clone()))});
        equivocators
            .iter()
            .for_each(|equivocator|
                      {let vote = !votes[*equivocator as usize];
                       messages.push(VoteCount::create_vote_msg(*equivocator as u32, vote))});
        (messages, equivocators, senders)
    }
}

proptest! {
    #![proptest_config(Config::with_cases(1000))]
    #[test]
    fn detect_equivocation(ref vote_tuple in votes(5, 5)) {
        let (messages, equivocators, nodes) = vote_tuple;
        let nodes = nodes.clone();
        let senders: Vec<u32> = (0..nodes as u32).collect();
        let weights: Vec<f64> =
            iter::repeat(1.0).take(nodes as usize).collect();
        let senders_weights = sender::Weights::new(
            senders
                .iter()
                .cloned()
                .zip(weights.iter().cloned())
                .collect(),
        );
        let sender_state = sender::State::new(
            senders_weights.clone(),
            0.0,
            None,
            LatestMsgs::empty(),
            0.0,
            HashSet::new(),
        );

        // here, only take one equivocation
        let single_equivocation: Vec<_> = messages[..nodes+1].iter().map(|message| message).collect();
        let equivocator = messages[nodes].sender();
        let (m0, _) =
            &Message::from_msgs(0, single_equivocation.clone(), &sender_state)
            .unwrap();
        let equivocations: Vec<_> = single_equivocation.iter().filter(|message| message.equivocates(&m0)).collect();
        assert!(if *equivocator == 0 {equivocations.len() == 1} else {equivocations.len() == 0}, "should detect sender 0 equivocating if sender 0 equivocates");
        // the following commented test should fail
        // assert_eq!(equivocations.len(), 1, "should detect sender 0 equivocating if sender 0 equivocates");

        let (m0, _) =
            &Message::from_msgs(0, messages.iter().map(|message| message).collect(), &sender_state)
            .unwrap();
        let equivocations: Vec<_> = messages.iter().filter(|message| message.equivocates(&m0)).collect();
        assert_eq!(equivocations.len(), 1, "should detect sender 0 equivocating if sender 0 equivocates");

        let sender_state = sender::State::new(
            senders_weights,
            0.0,
            None,
            LatestMsgs::empty(),
            equivocators.len() as f64,
            HashSet::new(),
        );
        let (m0, _) =
            &Message::from_msgs(0, messages.iter().map(|message| message).collect(), &sender_state)
            .unwrap();
        let equivocations: Vec<_> = messages.iter().filter(|message| message.equivocates(&m0)).collect();
        assert_eq!(equivocations.len(), 0, "equivocation absorbed in threshold");
    }
}
