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

#[macro_use]
extern crate serde_derive;

extern crate bincode;
extern crate blake2;
extern crate casper;
extern crate itertools;
extern crate serde;

use casper::util::hash::Hash;
use casper::util::id::Id;

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct Example {
    count: u64,
    int: i64,
}

impl Id for Example {
    type ID = Hash;
}

fn main() {
    let s = Example { count: 10, int: -4 };
    println!("{:?}", s);
    println!("ID {:?}", s.getid());
    let ser = s.serialize();
    println!("BIN {:?}", ser);
    let de = Example::deserialize(&ser[..]);
    println!("{:?}", de);
    assert_eq!(s, de.unwrap());
}
