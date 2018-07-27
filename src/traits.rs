use std::hash::{Hash};
use std::fmt::{Debug};
use message::{AbstractMsg};
use justification::{Justification};

pub trait Estimate: Hash + Clone + Ord + Send + Sync + Debug {
    type M: AbstractMsg<Estimate = Self>;
    type Data;
    fn mk_estimate(
        justification: &Justification<Self::M>,
        external_data: Option<Self::Data>,
    ) -> Option<Self>;
}

pub trait Sender: Hash + Clone + Ord + Eq + Send + Sync + Debug {}

pub trait Zero<T: PartialEq> {
    const ZERO: T;
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}
