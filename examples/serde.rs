#[macro_use]
extern crate serde_derive;

extern crate bincode;
extern crate blake2;
extern crate casper;
extern crate itertools;
extern crate serde;

use casper::traits::Id;
use casper::util::hash::Hash;

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct Example {
    count: u64,
    int: i64,
}

impl casper::traits::Id for Example {
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
