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

extern crate core_cbc_casper;

use std::collections::HashSet;

use core_cbc_casper::blockchain::Block;
use core_cbc_casper::justification::{Justification, LatestMessages};
use core_cbc_casper::message::Message;
use core_cbc_casper::validator;
use core_cbc_casper::ValidatorNameBlockData;

#[test]
fn partial_view() {
    // Test cases where not all validators see all messages.
    let validators: Vec<u32> = (0..5).collect();
    let weights = [1.0, 1.0, 2.0, 1.0, 1.1];

    let mut state = validator::State::new(
        validator::Weights::new(
            validators
                .iter()
                .cloned()
                .zip(weights.iter().cloned())
                .collect(),
        ),
        0.0,
        LatestMessages::empty(),
        1.0,
        HashSet::new(),
    );

    let genesis_block = Block::new(None, ValidatorNameBlockData::new(0));
    let latest_messages = Justification::empty();
    let genesis_block_message = Message::new(validators[0], latest_messages, genesis_block.clone());
    // (s0, w=1.0)   gen
    // (s1, w=1.0)
    // (s2, w=2.0)
    // (s3, w=1.0)
    // (s4, w=1.1)

    assert_eq!(
        &Block::from(&genesis_block_message),
        &genesis_block,
        "genesis block with None as prevblock"
    );

    state.update(&[&genesis_block_message]);
    let m1 = Message::from_validator_state(validators[1], &state.clone()).unwrap();
    // (s0, w=1.0)   gen
    // (s1, w=1.0)     \--m1
    // (s2, w=2.0)
    // (s3, w=1.0)
    // (s4, w=1.1)

    state.update(&[&genesis_block_message]);
    let m2 = Message::from_validator_state(validators[2], &state.clone()).unwrap();
    // (s0, w=1.0)   gen
    // (s1, w=1.0)    |\--m1
    // (s2, w=2.0)    \---m2
    // (s3, w=1.0)
    // (s4, w=1.1)

    state.update(&[&m1, &m2]);
    let m3 = Message::from_validator_state(validators[3], &state.clone()).unwrap();
    // (s0, w=1.0)   gen
    // (s1, w=1.0)    |\--m1
    // (s2, w=2.0)    \---m2
    // (s3, w=1.0)         \---m3
    // (s4, w=1.1)

    assert_eq!(
        m3.estimate(),
        &Block::new(Some(Block::from(&m2)), ValidatorNameBlockData::new(0)),
        "should build on top of m2 as validators[2] has more weight"
    );

    state.update(&[&m1]);
    let m4 = Message::from_validator_state(validators[4], &state.clone()).unwrap();
    // (s0, w=1.0)   gen
    // (s1, w=1.0)    |\--m1-------\
    // (s2, w=2.0)    \---m2       |
    // (s3, w=1.0)         \---m3  |
    // (s4, w=1.1)                 m4

    assert_eq!(
        m4.estimate(),
        &Block::new(Some(Block::from(&m1)), ValidatorNameBlockData::new(0)),
        "should build on top of m1 as thats the only message it saw"
    );

    state.update(&[&m3, &m2]);
    let m5 = Message::from_validator_state(validators[0], &state).unwrap();
    // (s0, w=1.0)   gen               m5
    // (s1, w=1.0)    |\--m1-------\   |
    // (s2, w=2.0)    \---m2       |   |
    // (s3, w=1.0)         \---m3--|---/
    // (s4, w=1.1)                 m4

    assert_eq!(
        m5.estimate(),
        &Block::new(Some(Block::from(&m3)), ValidatorNameBlockData::new(0)),
        "should build on top of m3"
    );

    let block = Block::from(&m3);
    assert_eq!(
        block,
        Block::new(Some(Block::from(&m2)), ValidatorNameBlockData::new(0))
    );
}

#[test]
fn full_view() {
    // Test a case where the last validator see all messages and build on top of the heaviest
    // one.
    let validators: Vec<u32> = (0..7).collect();
    let weights = [1.0, 1.0, 1.0, 1.0, 1.0, 1.1, 1.0];

    let mut state = validator::State::new(
        validator::Weights::new(
            validators
                .iter()
                .cloned()
                .zip(weights.iter().cloned())
                .collect(),
        ),
        0.0,
        LatestMessages::empty(),
        1.0,
        HashSet::new(),
    );

    let genesis_block = Block::new(None, ValidatorNameBlockData::new(0));
    let latest_messages = Justification::empty();
    let genesis_block_message = Message::new(validators[0], latest_messages, genesis_block);
    // (sg, w=1.0)   gen
    // (s0, w=1.0)
    // (s1, w=1.0)
    // (s2, w=1.0)
    // (s3, w=1.0)
    // (s4, w=1.1)
    // (s5, w=1.0)

    state.update(&[&genesis_block_message]);
    let m0 = Message::from_validator_state(validators[1], &state).unwrap();
    // (sg, w=1.0)   gen
    // (s0, w=1.0)     \--m0
    // (s1, w=1.0)
    // (s2, w=1.0)
    // (s3, w=1.0)
    // (s4, w=1.1)
    // (s5, w=1.0)

    state.update(&[&m0]);
    let m1 = Message::from_validator_state(validators[2], &state).unwrap();
    // (sg, w=1.0)   gen
    // (s0, w=1.0)     \--m0
    // (s1, w=1.0)         \--m1
    // (s2, w=1.0)
    // (s3, w=1.0)
    // (s4, w=1.1)
    // (s5, w=1.0)

    state.update(&[&genesis_block_message]);
    let m2 = Message::from_validator_state(validators[3], &state).unwrap();
    // (sg, w=1.0)   gen
    // (s0, w=1.0)    |\--m0
    // (s1, w=1.0)    |    \--m1
    // (s2, w=1.0)    \-----------m2
    // (s3, w=1.0)
    // (s4, w=1.1)
    // (s5, w=1.0)

    state.update(&[&m2]);
    let m3 = Message::from_validator_state(validators[4], &state).unwrap();
    // (sg, w=1.0)   gen
    // (s0, w=1.0)    |\--m0
    // (s1, w=1.0)    |    \--m1
    // (s2, w=1.0)    \-----------m2
    // (s3, w=1.0)                 \--m3
    // (s4, w=1.1)
    // (s5, w=1.0)

    state.update(&[&m2]);
    let m4 = Message::from_validator_state(validators[5], &state).unwrap();
    // (sg, w=1.0)   gen
    // (s0, w=1.0)    |\--m0
    // (s1, w=1.0)    |    \--m1
    // (s2, w=1.0)    \-----------m2
    // (s3, w=1.0)                |\--m3
    // (s4, w=1.1)                \-------m4
    // (s5, w=1.0)

    state.update(&[&m0, &m1, &m2, &m3, &m4]);
    let m5 = Message::from_validator_state(validators[6], &state).unwrap();
    // (sg, w=1.0)   gen
    // (s0, w=1.0)    |\--m0
    // (s1, w=1.0)    |    \--m1
    // (s2, w=1.0)    \-----------m2
    // (s3, w=1.0)                |\--m3
    // (s4, w=1.1)                \-------m4
    // (s5, w=1.0)                         \--m5

    assert_eq!(
        m5.estimate(),
        &Block::new(Some(Block::from(&m4)), ValidatorNameBlockData::new(0)),
        "should build on top of b4"
    );
}
