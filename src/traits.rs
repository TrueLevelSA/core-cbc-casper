use std::hash::{Hash};
use std::fmt::{Debug};

use message::{CasperMsg};
use justification::{Justification, SenderState};
use senders_weight::{SendersWeight};
use std::collections::{BTreeSet, HashSet, HashMap};
// use weight_unit::WeightUnit;

pub trait Estimate: Hash + Clone + Ord + Send + Sync + Debug + Data {
    type M: CasperMsg<Estimate = Self>;
    fn mk_estimate(
        latest_msgs: &Justification<Self::M>,
        finalized_msg: Option<&Self::M>,
        senders_weights: &SendersWeight<
            <<Self as Estimate>::M as CasperMsg>::Sender,
        >,
        external_data: Option<<Self as Data>::Data>,
    ) -> Self;
}

pub trait Data {
    type Data;
    fn is_valid(&Self::Data) -> bool;
}

pub trait Sender: Hash + Clone + Ord + Eq + Send + Sync + Debug {}

pub trait Node: Clone + Send + Sync + Debug {
    type M: CasperMsg;
    type WeightUnit; //
    fn get_senders_weight(&self) -> &SendersWeight<<<Self as Node>::M as CasperMsg>::Sender>;
    fn get_latest_msgs(&self) -> &Justification<Self::M>;
    fn get_equivocators(&self) -> &HashSet<<<Self as Node>::M as CasperMsg>::Sender>;
    fn get_thr(&self) -> Self::WeightUnit;
    fn get_state_fault_weight(&self) -> Self::WeightUnit;
    fn new(
        senders_weight: SendersWeight<<<Self as Node>::M as CasperMsg>::Sender>,
        last_msgs: Justification<Self::M>,
        equivocators: HashSet<<<Self as Node>::M as CasperMsg>::Sender>,
        thr: Self::WeightUnit,
        state_fault_weight: Self::WeightUnit,
    ) -> Self;
}

pub trait Zero<T: PartialEq> {
    const ZERO: T;
    fn is_zero(val: &T) -> bool {
        val == &Self::ZERO
    }
}
