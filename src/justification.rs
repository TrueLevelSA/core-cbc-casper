use std::collections::{BTreeSet, HashSet, HashMap, VecDeque};
use std::collections::hash_map::{Iter as HashIter, Keys};
use std::collections::hash_set::{Iter as HSetIter};
use std::collections::btree_set::Iter;
use std::fmt::{Debug, Formatter};
// use std::io::{Error};

use rayon::collections::btree_set::Iter as ParIter;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use message::{CasperMsg, Message};
use weight_unit::{WeightUnit};
use traits::{Zero, Estimate, Data};
use senders_weight::SendersWeight;

#[derive(Eq, Ord, PartialOrd, PartialEq, Clone, Default, Hash)]
pub struct Justification<M: CasperMsg>(BTreeSet<M>);

impl<M: CasperMsg> Justification<M> {
    // Re-exports from BTreeSet wrapping M
    pub fn new() -> Self {
        Justification(BTreeSet::new())
    }
    pub fn from_msgs(
        msgs: Vec<M>,
        sender_state: &SenderState<M>,
    ) -> (Self, SenderState<M>) {
        let mut j = Justification::new();
        let msgs: HashSet<_> = msgs.iter().collect();
        let (_, sender_state) = j.faulty_inserts(msgs, sender_state);
        (j, sender_state)
    }
    pub fn iter(&self) -> Iter<M> {
        self.0.iter()
    }
    pub fn par_iter(&self) -> ParIter<M> {
        self.0.par_iter()
    }
    pub fn contains(&self, msg: &M) -> bool {
        self.0.contains(msg)
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn insert(&mut self, msg: M) -> bool {
        self.0.insert(msg)
    }
    fn head(&self) -> Option<&M> {
        self.0.iter().next()
    }

    // reexport from Estimate impl
    pub fn mk_estimate(
        &self,
        finalized_msg: Option<&M>,
        equivocators: &HashSet<M::Sender>,
        senders_weights: &SendersWeight<<M as CasperMsg>::Sender>,
        data: Option<<<M as CasperMsg>::Estimate as Data>::Data>,
    ) -> M::Estimate {
        let latest_msgs = LatestMsgs::from(self);
        let latest_msgs_honest =
            LatestMsgsHonest::from_latest_msgs(&latest_msgs, equivocators);
        M::Estimate::mk_estimate(
            &latest_msgs_honest,
            finalized_msg,
            senders_weights,
            data,
        )
    }

    // Custom functions
    /// get the additional equivocators upon insertion of msg to the state. note
    /// that if equivocator is a recurrent equivocator, it will be found again
    /// here. i believe the weight of an equivocator has to be set to ZERO
    /// immediately upon finding an equivocation
    fn get_equivocators(&self, msg_new: &M) -> HashSet<M::Sender> {
        self.par_iter()
            .filter_map(|msg_old| {
                if msg_old.equivocates(&msg_new) {
                    Some(msg_old.get_sender())
                }
                else {
                    None
                }
            })
            .cloned()
            .collect()
    }
    /// get msgs and fault weight overhead and equivocators overhead sorted
    /// by fault weight overhead
    fn sort_by_faultweight<'z>(
        &self,
        senders_weights: SendersWeight<M::Sender>,
        equivocators: HashSet<M::Sender>,
        msgs: HashSet<&'z M>,
    ) -> Vec<&'z M> {
        let mut msgs_sorted_by_faultw: Vec<_> = msgs
            .iter()
            .enumerate()
            .filter_map(|(outer_i, &msg)| {
                // equivocations in relation to state
                let state_equivocators: HashSet<_> = self.get_equivocators(msg);

                // equivocations present within the current latest_msgs set that
                // we're trying to insert to the state
                let pairwise_equivocators: HashSet<_> = msgs
                        .iter()
                    // ensures we check only once per pair [(a, b)] and not
                    // [(a, b), (b, a)]
                        .skip(outer_i)
                        .filter_map(|m| {
                            if m.equivocates(msg) { Some(m.get_sender()) }
                            else { None }
                        })
                        .cloned()
                        .collect();

                let msg_equivocators: HashSet<_> = state_equivocators
                        .union(&pairwise_equivocators)
                    // take only the equivocators that are not yet on the
                    // equivocator set as the others already have their
                    // weight counted into the state fault count
                        .filter(|equivocator| !equivocators.contains(equivocator))
                        .cloned()
                        .collect();
                let msg_faultweight_overhead =
                    senders_weights.sum_weight_senders(&msg_equivocators);
                // sum_weight_senders returns nan if a sender is not found
                if msg_faultweight_overhead.is_nan() {
                    None
                }
                else {
                    Some((msg, msg_faultweight_overhead))
                }
            })
            .collect();
        let _ = msgs_sorted_by_faultw.sort_unstable_by(|(_, w0), (_, w1)| {
            w0.partial_cmp(w1).unwrap_or(::std::cmp::Ordering::Greater) // tie breaker
        });

        // return a Vec<CasperMsg>
        msgs_sorted_by_faultw
            .iter()
            .map(|(m, _)| m)
            .cloned()
            .collect()
    }
    /// insert msgs to the Justification, accepting up to $thr$ faults by
    /// weight, returns success=true if at least one msg of the set gets
    /// successfully included to the justification
    pub fn faulty_inserts(
        &mut self,
        msgs: HashSet<&M>,
        sender_state: &SenderState<M>,
    ) -> (bool, SenderState<M>) {
        // // do the actual insertions to the state
        // self.sort_by_faultweight(
        //     sender_state.senders_weights.clone(),
        //     sender_state.equivocators.clone(),
        //     msgs,
        // )
        msgs.iter().fold(
            (false, sender_state.clone()),
            |(success, sender_state), &msg| {
                let (success_prime, sender_state_prime) =
                    self.faulty_insert_with_slash(msg, sender_state);
                (success || success_prime, sender_state_prime)
            },
        )
    }

    /// this function makes no assumption on how to treat the equivocator. it
    /// adds the msg to the justification only if it will not cross the fault
    /// tolerance thr
    pub fn faulty_insert(
        &mut self,
        msg: &M,
        sender_state: &SenderState<M>,
    ) -> (bool, SenderState<M>) {
        let sender_state = sender_state.clone();
        let msg_equivocators_overhead: HashSet<_> = self.get_equivocators(msg)
            .iter()
        // take only the msg_equivocators_overhead that are not yet on the
        // equivocator set as the others already have their weight counted into
        // the state fault count
            .filter(|equivocator| !sender_state.equivocators.contains(equivocator))
            .cloned()
            .collect();
        let msg_fault_weight_overhead = sender_state
            .senders_weights
            .sum_weight_senders(&msg_equivocators_overhead);
        let new_fault_weight = sender_state
            .state_fault_weight
            .clone()
            .map(|w| w + msg_fault_weight_overhead);
        let equivocators = sender_state
            .equivocators
            .union(&msg_equivocators_overhead)
            .cloned()
            .collect();

        new_fault_weight
            .and_then(|w| {
                let sender_state = sender_state.clone();
                if w <= sender_state.thr {
                    let success = self.insert(msg.clone());
                    let sender_state = if success {
                        SenderState {
                            state_fault_weight: new_fault_weight,
                            equivocators,
                            ..sender_state
                        }
                    }
                    else {
                        sender_state
                    };
                    Some((success, sender_state))
                }
                else {
                    None
                }
            })
            .unwrap_or((false, sender_state))

        // conflicting message NOT added to the set as it crosses the fault
        // weight thr OR msg_fault_weight_overhead is NAN (from the unwrap)
    }
    /// this function sets the weight of the equivocator to zero right away
    /// (returned on SenderState) and add his message to the state, since now his
    /// equivocation doesnt count to the state fault weight anymore
    pub fn faulty_insert_with_slash(
        &mut self,
        msg: &M,
        mut sender_state: SenderState<M>,
    ) -> (bool, SenderState<M>) {
        let is_equivocation = sender_state.latest_msgs.equivocate(msg);
        if is_equivocation {
            let sender = msg.get_sender();
            sender_state.equivocators.insert(sender.clone());
            sender_state
                .senders_weights
                .insert(sender.clone(), WeightUnit::ZERO);
        }
        sender_state.latest_msgs.update(msg);
        let success = self.insert(msg.clone());
        (success, sender_state)
    }

    pub fn get_subtree_weights(
        &self,
        finalized_msg: Option<&M>, // stops sum at finalized_msg
        senders_weights: &SendersWeight<M::Sender>,
    ) -> Result<HashMap<M, WeightUnit>, &'static str> {
        fn recursor<M>(
            m: &M,
            finalized_msg: Option<&M>, // if None, runs all the way to genesis msgs
            senders_weights: &SendersWeight<M::Sender>,
            all_senders: &HashSet<M::Sender>,
            mut senders_referred: HashSet<M::Sender>,
            initial_weight: WeightUnit,
        ) -> WeightUnit
        where
            M: CasperMsg,
        {
            m.get_justification().iter().fold(
                initial_weight,
                |weight_referred, m_prime| {
                    // base case
                    if finalized_msg
                        .map(|f_msg| {
                            f_msg == m_prime || !m_prime.depends(f_msg) // TODO: check if needed
                        })
                        .unwrap_or(false)
                    {
                        weight_referred
                    }
                    else {
                        let sender_current = m_prime.get_sender();
                        // it fails to insert sender_current, if sender_current is
                        // already in set
                        let weight_referred = if senders_referred
                            .insert(sender_current.clone())
                        {
                            weight_referred
                                + senders_weights
                                    .get_weight(&sender_current)
                                    .unwrap_or(WeightUnit::ZERO)
                        }
                        else {
                            weight_referred
                        };

                        recursor(
                            m_prime,
                            finalized_msg,
                            senders_weights,
                            all_senders,
                            senders_referred.clone(),
                            weight_referred,
                        )
                    }
                },
            )
        };
        // initial state, trigger recursion
        match &senders_weights.get_senders() {
            Ok(all_senders) => Ok(self
                .iter()
                .map(|m| {
                    let sender_current = m.get_sender();
                    let senders_referred: HashSet<
                        M::Sender,
                    > = [sender_current.clone()].iter().cloned().collect();
                    let initial_weight = senders_weights
                        .get_weight(&sender_current)
                        .unwrap_or(WeightUnit::ZERO);
                    (
                        m.clone(),
                        recursor(
                            m,
                            finalized_msg,
                            senders_weights,
                            all_senders,
                            senders_referred.clone(),
                            initial_weight,
                        ),
                    )
                })
                .collect()),
            Err(e) => Err(e),
        }
    }
}

impl<M: CasperMsg> Debug for Justification<M> {
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

pub struct LatestMsgsHonest<M: CasperMsg>(HashSet<M>);
impl<M: CasperMsg> LatestMsgsHonest<M> {
    fn new() -> Self {
        LatestMsgsHonest(HashSet::new())
    }
    fn insert(&mut self, msg: M) -> bool {
        self.0.insert(msg)
    }
    pub fn from_latest_msgs(
        latest_msgs: &LatestMsgs<M>,
        equivocators: &HashSet<M::Sender>,
    ) -> Self {
        latest_msgs
            .iter()
            .filter_map(|(sender, msgs)| {
                if equivocators.contains(sender) || msgs.len() != 1 {
                    None
                }
                else {
                    msgs.iter().next()
                }
            })
            .fold(LatestMsgsHonest::new(), |mut acc, msg| {
                acc.insert(msg.clone());
                acc
            })
    }
    pub fn iter(&self) -> HSetIter<M> {
        self.0.iter()
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn mk_estimate(
        &self,
        finalized_msg: Option<&M>,
        senders_weights: &SendersWeight<<M as CasperMsg>::Sender>,
        data: Option<<<M as CasperMsg>::Estimate as Data>::Data>,
    ) -> M::Estimate {
        M::Estimate::mk_estimate(
            &self,
            finalized_msg,
            senders_weights,
            data,
        )
    }
}

#[derive(Eq, PartialEq, Clone, Default, Debug)]
pub struct LatestMsgs<M: CasperMsg>(
    HashMap<<M as CasperMsg>::Sender, HashSet<M>>,
);
impl<M: CasperMsg> LatestMsgs<M> {
    pub fn new() -> Self {
        LatestMsgs(HashMap::new())
    }
    pub fn insert(
        &mut self,
        k: M::Sender,
        v: HashSet<M>,
    ) -> Option<HashSet<M>> {
        self.0.insert(k, v)
    }
    pub fn contains_key(&self, k: &M::Sender) -> bool {
        self.0.contains_key(k)
    }
    pub fn get(&self, k: &M::Sender) -> Option<&HashSet<M>> {
        self.0.get(k)
    }
    pub fn iter(&self) -> HashIter<M::Sender, HashSet<M>> {
        self.0.iter()
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn keys(&self) -> Keys<M::Sender, HashSet<M>> {
        self.0.keys()
    }
    pub fn update(&mut self, new_message: &M) -> bool {
        let sender: &M::Sender = new_message.get_sender();
        if let Some(latest_msgs_from_sender) = self.get(sender).cloned() {
            let later_than_new: HashSet<M> = latest_msgs_from_sender
                .iter()
                .filter(|current_message| current_message.depends(new_message))
                .cloned()
                .collect();
            if later_than_new.is_empty() {
                let mut new_later_than: HashSet<M> = latest_msgs_from_sender
                    .iter()
                    .filter(|current_message| {
                        !new_message.depends(current_message)
                    })
                    .cloned()
                    .collect();
                new_later_than.insert(new_message.clone());
                self.insert(sender.clone(), new_later_than);
                true
            }
            else {
                false
            }
        }
        else {
            self.insert(
                sender.clone(),
                [new_message.clone()].iter().cloned().collect(),
            );
            true
        }
    }
    fn equivocate(&self, msg_new: &M) -> bool {
        self.get(msg_new.get_sender())
            .map(|latest_msgs| {
                latest_msgs.iter().any(|m| m.equivocates(&msg_new))
            })
            .unwrap_or(false)
    }
}

impl<'z, M: CasperMsg> From<&'z Justification<M>> for LatestMsgs<M> {
    fn from(j: &Justification<M>) -> Self {
        let mut latest_msgs: LatestMsgs<M> = LatestMsgs::new();
        let mut queue: VecDeque<(M)> = j.iter().cloned().collect();
        while let Some(msg) = queue.pop_front() {
            if latest_msgs.update(&msg) {
                msg.get_justification()
                    .iter()
                    .for_each(|m| queue.push_back(m.clone()));
            }
        }
        latest_msgs
    }
}
// impl<'z, M: CasperMsg> From<&'z Justification<M>> for LatestMsgs<M> {
//     fn from(j: &Justification<M>) -> Self {
//         fn recur_func<M: CasperMsg>(
//             j: &Justification<M>,
//             latest_msgs: LatestMsgs<M>,
//         ) -> LatestMsgs<M> {
//             // TODO: this should be breadth first like ghost in blockchain
//             j.iter().fold(latest_msgs, |mut acc, m| {
//                 acc.update(m);
//                 recur_func(m.get_justification(), acc)
//             })
//         }
//         recur_func(j, LatestMsgs::new())
//     }
// }

#[derive(Debug, Clone)]
pub struct SenderState<M: CasperMsg> {
    state_fault_weight: Option<WeightUnit>,
    thr: WeightUnit,
    senders_weights: SendersWeight<M::Sender>,
    my_last_msg: Option<M>,
    latest_msgs: LatestMsgs<M>,
    equivocators: HashSet<M::Sender>, // FIXME: put it here as its needed on the same context as
}

impl<M: CasperMsg> SenderState<M> {
    pub fn new(
        senders_weights: SendersWeight<M::Sender>,
        state_fault_weight: Option<WeightUnit>,
        my_last_msg: Option<M>,
        latest_msgs: LatestMsgs<M>,
        thr: WeightUnit,
        equivocators: HashSet<M::Sender>,
    ) -> Self {
        SenderState {
            senders_weights,
            equivocators,
            state_fault_weight,
            thr,
            my_last_msg,
            latest_msgs,
        }
    }
    pub fn get_equivocators(&self) -> &HashSet<M::Sender> {
        &self.equivocators
    }
    pub fn get_senders_weights(&self) -> &SendersWeight<M::Sender> {
        &self.senders_weights
    }
    pub fn get_my_last_msg(&self) -> &Option<M> {
        &self.my_last_msg
    }
    pub fn get_latest_msgs(&self) -> &LatestMsgs<M> {
        &self.latest_msgs
    }
}

#[cfg(test)]
mod justification {
    use super::*;

    use example::vote_count::{VoteCount};

    #[test]
    fn children_weight() {
        use example::blockchain::{BlockMsg, Block};

        let (sender0, sender1, sender2, sender3) = (0, 1, 2, 3); // miner identities
        let (weight0, weight1, weight2, weight3) = (2., 4., 8., 16.); // and their corresponding weights
        let senders_weights = SendersWeight::new(
            [
                (sender0, weight0),
                (sender1, weight1),
                (sender2, weight2),
                (sender3, weight3),
            ].iter()
                .cloned()
                .collect(),
        );
        let txs = BTreeSet::new();
        let genesis_block = Block::new(None, sender0, txs.clone()); // estimate of the first casper message
        let justification = Justification::new();
        let genesis_msg =
            BlockMsg::new(sender0, justification, genesis_block.clone());
        assert_eq!(
            genesis_msg.get_estimate(),
            &genesis_block,
            "genesis block with None as prev_block"
        );
        // genesis_msg(s=0, w=2) <- m1(s=1, w=4) <- m2(s=2, w=8) <- m3(s=3, w=16)
        // weights:       2               6               14               30
        let mut justification = Justification::new();
        assert!(justification.insert(genesis_msg.clone()));
        let subtree_weights = justification
            .get_subtree_weights(None, &senders_weights)
            .unwrap();
        let (_msg, weight) = subtree_weights.iter().next().unwrap();
        assert_eq!(weight, &2.0);
        let proto_b1 = Block::new(None, sender1, txs.clone());
        let b1 =
            Block::from_prevblock_msg(Some(genesis_msg), proto_b1).unwrap();
        let m1 = BlockMsg::new(sender1, justification, b1);

        let mut justification = Justification::new();
        assert!(justification.insert(m1.clone()));
        let subtree_weights = justification
            .get_subtree_weights(None, &senders_weights)
            .unwrap();
        let (_msg, weight) = subtree_weights.iter().next().unwrap();
        assert_eq!(weight, &6.0);
        let proto_b2 = Block::new(None, sender2, txs.clone());
        let b2 = Block::from_prevblock_msg(Some(m1), proto_b2).unwrap();
        let m2 = BlockMsg::new(sender2, justification, b2);

        let mut justification = Justification::new();
        assert!(justification.insert(m2.clone()));
        let subtree_weights = justification
            .get_subtree_weights(None, &senders_weights)
            .unwrap();
        let (_msg, weight) = subtree_weights.iter().next().unwrap();
        assert_eq!(weight, &14.0);
        let proto_b3 = Block::new(None, sender3, txs);
        let b3 = Block::from_prevblock_msg(Some(m2), proto_b3).unwrap();
        let m3 = BlockMsg::new(sender3, justification, b3);

        let mut justification = Justification::new();
        assert!(justification.insert(m3.clone()));
        let subtree_weights = justification
            .get_subtree_weights(None, &senders_weights)
            .unwrap();
        let (_msg, weight) = subtree_weights.iter().next().unwrap();
        assert_eq!(weight, &30.0);
    }

    #[test]
    fn faulty_inserts_sorted() {
        let senders_weights = SendersWeight::new(
            [(0, 1.0), (1, 2.0), (2, 3.0)].iter().cloned().collect(),
        );

        let v0 = &VoteCount::create_vote_msg(0, false);
        let v0_prime = &VoteCount::create_vote_msg(0, true);
        let v1 = &VoteCount::create_vote_msg(1, true);
        let v1_prime = &VoteCount::create_vote_msg(1, false);
        let v2 = &VoteCount::create_vote_msg(2, true);
        let v2_prime = &VoteCount::create_vote_msg(2, false);
        let weights = SenderState {
            senders_weights: senders_weights.clone(),
            state_fault_weight: Some(0.0),
            my_last_msg: None,
            thr: 3.0,
            equivocators: HashSet::new(),
            latest_msgs: LatestMsgs::new(),
        };
        let mut j = Justification::new();
        let sorted_msgs = j.sort_by_faultweight(
            senders_weights,
            weights.get_equivocators().clone(),
            vec![v2, v2_prime, v1, v1_prime, v0, v0_prime]
                .iter()
                .cloned()
                .collect(),
        );
        let (_, weights) = sorted_msgs.iter().fold(
            (false, weights),
            |(success, weights), m| {
                let (s, w) = j.faulty_insert(m, &weights);
                (s || success, w)
            },
        );
        assert_eq!(j.len(), 5);
        assert_eq!(weights.state_fault_weight, Some(3.0));
    }
    #[test]
    fn faulty_inserts() {
        let senders_weights = SendersWeight::new(
            [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect(),
        );
        let v0 = &VoteCount::create_vote_msg(0, false);
        let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = &VoteCount::create_vote_msg(1, true);
        let mut j0 = Justification::new();
        let weights = SenderState {
            senders_weights: senders_weights.clone(),
            state_fault_weight: Some(0.0),
            my_last_msg: None,
            thr: 0.0,
            equivocators: HashSet::new(),
            latest_msgs: LatestMsgs::new(),
        };
        let (success, _) =
            j0.faulty_inserts([v0].iter().cloned().collect(), &weights);
        assert!(success);
        let (m0, _weights) = &Message::from_msgs(
            0,
            vec![v0],
            None,
            &weights,
            None as Option<VoteCount>,
        ).unwrap();
        // let m0 = &Message::new(0, justification, estimate);
        let mut j1 = Justification::new();
        let (success, _) = j1.faulty_inserts(
            vec![v1].iter().cloned().collect(),
            &SenderState {
                senders_weights: senders_weights.clone(),
                state_fault_weight: Some(0.0),
                my_last_msg: None,
                thr: 0.0,
                equivocators: HashSet::new(),
                latest_msgs: LatestMsgs::new(),
            },
        );
        assert!(success);
        let (success, _) = j1.faulty_inserts(
            vec![m0].iter().cloned().collect(),
            &SenderState {
                senders_weights: senders_weights.clone(),
                state_fault_weight: Some(0.0),
                my_last_msg: None,
                thr: 0.0,
                equivocators: HashSet::new(),
                latest_msgs: LatestMsgs::new(),
            },
        );
        assert!(success);
        let (success, _) = j1.faulty_insert(
            v0_prime,
            &SenderState {
                senders_weights: senders_weights.clone(),
                state_fault_weight: Some(0.0),
                my_last_msg: None,
                thr: 0.0,
                equivocators: HashSet::new(),
                latest_msgs: LatestMsgs::new(),
            },
        );
        assert!(
            !success,
            "$v0_prime$ should conflict with $v0$ through $m0$, and we should reject as our fault tolerance thr is zero"
        );
        let (success, _) = j1.clone().faulty_insert(
            v0_prime,
            &SenderState {
                senders_weights: senders_weights.clone(),
                state_fault_weight: Some(0.0),
                my_last_msg: None,
                thr: 1.0,
                equivocators: HashSet::new(),
                latest_msgs: LatestMsgs::new(),
            },
        );
        assert!(success,
            "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set"
        );
        let (_, sender_state) = j1.clone().faulty_insert(
            v0_prime,
            &SenderState {
                senders_weights: senders_weights.clone(),
                state_fault_weight: Some(0.0),
                my_last_msg: None,
                thr: 1.0,
                equivocators: HashSet::new(),
                latest_msgs: LatestMsgs::new(),
            },
        );
        assert_eq!(
            sender_state.state_fault_weight,
            Some(1.0),
            "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept
this fault as it doesnt cross the fault threshold for the set, and thus the
state_fault_weight should be incremented to 1.0"
        );
        let (success, _) = j1.clone().faulty_insert(
            v0_prime,
            &SenderState {
                senders_weights: senders_weights.clone(),
                state_fault_weight: Some(0.1),
                my_last_msg: None,
                thr: 1.0,
                equivocators: HashSet::new(),
                latest_msgs: LatestMsgs::new(),
            },
        );
        assert!(!success,
            "$v0_prime$ conflicts with $v0$ through $m0$, and we should not accept this fault as the fault threshold gets crossed for the set"
        );
        let (_, sender_state) = j1.clone().faulty_insert(
            v0_prime,
            &SenderState {
                senders_weights: senders_weights.clone(),
                state_fault_weight: Some(0.1),
                my_last_msg: None,
                thr: 1.0,
                equivocators: HashSet::new(),
                latest_msgs: LatestMsgs::new(),
            },
        );
        assert_eq!(sender_state.state_fault_weight, Some(0.1),
            "$v0_prime$ conflicts with $v0$ through $m0$, and we should NOT accept this fault as the fault threshold gets crossed for the set, and thus the state_fault_weight should not be incremented"
        );
        let (success, _) = j1.clone().faulty_insert(
            v0_prime,
            &SenderState {
                senders_weights: senders_weights.clone(),
                state_fault_weight: Some(1.0),
                my_last_msg: None,
                thr: 2.0,
                equivocators: HashSet::new(),
                latest_msgs: LatestMsgs::new(),
            },
        );
        assert!(success,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should accept this fault as the thr doesnt get crossed for the set"
        );

        let senders_weights = SendersWeight::new([].iter().cloned().collect());
        // bug found
        let (success, _) = j1.clone().faulty_insert(
            v0_prime,
            &SenderState {
                senders_weights: senders_weights.clone(),
                state_fault_weight: Some(1.0),
                my_last_msg: None,
                thr: 2.0,
                equivocators: HashSet::new(),
                latest_msgs: LatestMsgs::new(),
            },
        );
        assert!(
            !success,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the sender, which could be Infinity"
        );
        let (_, sender_state) = j1.clone().faulty_insert(
            v0_prime,
            &SenderState {
                senders_weights: senders_weights.clone(),
                state_fault_weight: Some(1.0),
                my_last_msg: None,
                thr: 2.0,
                equivocators: HashSet::new(),
                latest_msgs: LatestMsgs::new(),
            },
        );
        assert_eq!(
                sender_state.state_fault_weight,
            Some(1.0),
            "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the sender, which could be Infinity, and thus the state_fault_weight should be unchanged"
        );
    }
}
