use std::hash::{Hash};
use std::fmt::{Debug};
use message::{AbstractMsg};
use justification::{Justification, Weights};

pub trait Estimate: Hash + Clone + Ord + Send + Sync + Debug {
    type M: AbstractMsg<Estimate = Self>;
    type Data;
    fn mk_estimate(
        latest_msgs: Vec<&Self::M>,
        weights: &Weights<<<Self as Estimate>::M as AbstractMsg>::Sender>,
        external_data: Option<Self::Data>,
    ) -> (
        Option<Self>,
        Justification<Self::M>,
        Weights<<<Self as Estimate>::M as AbstractMsg>::Sender>,
    );
}

pub trait Sender: Hash + Clone + Ord + Eq + Send + Sync + Debug {}

pub trait Zero<T: PartialEq> {
    const ZERO: T;
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}
