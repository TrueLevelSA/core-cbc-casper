use std::hash::{Hash};
use std::fmt::{Debug};
use message::{AbstractMsg};
use justification::{Justification, Weights};

pub trait Estimate: Hash + Clone + Ord + Send + Sync + Debug {
    type M: AbstractMsg<Estimate = Self>;
    fn mk_estimate(
        latest_msgs: &Justification<Self::M>,
        finalized_msg: Option<&Self::M>,
        weights: &Weights<<<Self as Estimate>::M as AbstractMsg>::Sender>,
        external_data: Option<<<Self as Estimate>::M as AbstractMsg>::Data>,
    ) -> Self;
}

pub trait Data: Clone + Eq + Sync + Send + Debug + Ord + Sized {}

pub trait Sender: Hash + Clone + Ord + Eq + Send + Sync + Debug {}

pub trait Zero<T: PartialEq> {
    const ZERO: T;
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}
