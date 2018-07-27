use std::hash::{Hash};
use std::fmt::{Debug};
use message::{AbstractMsg};
use justification::{Justification};

pub trait Estimate: Hash + Clone + Ord + Send + Sync + Debug {
    type M: AbstractMsg<E = Self>;
    type D;
    // TODO: this estimator is good only if there's no external dependency, not
    // good for blockchain consensus
    // fn mk_estimate(justification: &Justification<Self::M>) -> Self;
    fn mk_estimate(
        justification: &Justification<Self::M>,
        external_data: Option<Self::D>,
    ) -> Self;
    // fn mk_estimate(justification: &Justification<Self::M>) -> Self;
}

pub trait Sender: Hash + Clone + Ord + Eq + Send + Sync + Debug {}

pub trait Zero<T: PartialEq> {
    const ZERO: T;
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}
