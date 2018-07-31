use std::hash::{Hash};
use std::fmt::{Debug};
use message::{AbstractMsg};
use justification::{Justification, Weights};

pub trait Estimate: Hash + Clone + Ord + Send + Sync + Debug {
    type M: AbstractMsg<Estimate = Self, Sender = Self::Sender>;
    type Sender: Sender;
    type Data: Data;
    fn mk_estimate(
        latest_msgs: &Justification<Self::M>,
        weights: &Weights<Self::Sender>,
        external_data: Option<Self::Data>,
    ) ->  Option<Self>;
}

pub trait Data: Clone + Eq + Sync + Send + Debug {}

pub trait Sender: Hash + Clone + Ord + Eq + Send + Sync + Debug {}

pub trait Zero<T: PartialEq> {
    const ZERO: T;
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}
