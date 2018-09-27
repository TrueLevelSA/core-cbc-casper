#[macro_use]
extern crate serde_derive;

extern crate serde;
extern crate bincode;
extern crate blake2;
extern crate itertools;
extern crate casper;

use itertools::Itertools;
use casper::traits::{Serialize, Deserialize, Id};
use blake2::{Blake2b, Digest};

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct Example {
    count: u64,
    int: i64,
}

impl casper::traits::Serialize for Example {
    fn serialize(&self) -> Vec<u8> {
        bincode::serialize(self).unwrap()
    }
}

impl casper::traits::Deserialize for Example {
    fn deserialize(bin: &[u8]) -> Result<Example, ()> {
        match bincode::deserialize(bin) {
            Ok(res) => Ok(res),
            _ => Err(()),
        }
    }
}

impl casper::traits::Id for Example {
    type ID = [u8; 64];

    fn hash(data: &[u8]) -> [u8; 64] {
        let mut res = [0u8; 64];
        res.copy_from_slice(&Blake2b::digest(data));
        res
    }
}

fn main() {
    let s = Example { count: 10, int: -4 };
    println!("{:?}", s);
    println!("ID {:02x}", s.getid().iter().format(""));
    let ser = s.serialize();
    println!("BIN {:?}", ser);
    let de = Example::deserialize(&ser[..]);
    println!("{:?}", de);
    assert_eq!(s, de.unwrap());
}

