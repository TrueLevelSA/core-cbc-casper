use std::hash::{Hash};
use std::fmt::{Debug};
use message::{AbstractMsg};
use justification::{Justification, Weights};

pub trait Estimate: Hash + Clone + Ord + Send + Sync + Debug {
    type M: AbstractMsg<Estimate = Self, Sender = Self::Sender>;
    type Sender: Sender;
    fn mk_estimate<D: Data>(
        latest_msgs: Vec<&Self::M>,
        weights: &Weights<Self::Sender>,
        external_data: Option<D>,
    ) -> (
        Option<Self>,
        Justification<<Self as Estimate>::M>,
        Weights<Self::Sender>,
    );
}

pub trait Data: Clone + Eq + Sync + Send + Debug {}

pub trait Sender: Hash + Clone + Ord + Eq + Send + Sync + Debug {}

pub trait Zero<T: PartialEq> {
    const ZERO: T;
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}
