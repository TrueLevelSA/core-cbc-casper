use std::hash::{Hash};
use std::fmt::{Debug};
use message::{AbstractMsg};
use justification::{Justification};

pub trait Estimate: Hash + Clone + Ord + Send + Sync + Debug {
    type M: AbstractMsg<E = Self>;
    // type D: ExternalData;
    // TODO: this estimator is good only if there's no external dependency, not
    // good for blockchain consensus
    fn estimator(justification: &Justification<Self::M>) -> Self;
    // fn estimator(
    //     justification: &Justification<Self::M>,
    //     external_data: Option<Self::D>,
    // ) -> Self;
    // fn estimator(justification: &Justification<Self::M>) -> Self;
}

// pub trait ExternalData {
//     type M: AbstractMsg;
//     type D;
//     fn is_valid(
//         justification: &Justification<Self::M>,
//         external_data: Self::D,
//     ) -> bool;
//     fn make_estimate(
//         justification: &Justification<Self::M>,
//         external_data: Self::D,
//     ) -> Self::M::E;
// }

pub trait Sender: Hash + Clone + Ord + Eq + Send + Sync + Debug {}

pub trait Zero<T: PartialEq> {
    const ZERO: T;
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}
