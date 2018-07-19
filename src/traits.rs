use std::hash::{Hash};
use std::fmt::{Debug};
use message::{AbstractMsg};
use justification::{Justification};

pub trait Estimate: Hash + Clone + Ord + Send + Sync + Debug {
    type M: AbstractMsg<E = Self>;
    // TODO: this estimator is good only if there's no external dependency, not
    // good for blockchain consensus
    fn estimator(justification: &Justification<Self::M>) -> Self;
    // fn estimator2<D: ExternalData>(justification: &Justification<Self::M>, extra_data: Option<D>) -> Self;
    // fn estimator(justification: &Justification<Self::M>) -> Self;
}

pub trait Sender: Hash + Clone + Ord + Eq + Send + Sync + Debug {}

pub trait Zero<T: PartialEq> {
    const ZERO: T;
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}
