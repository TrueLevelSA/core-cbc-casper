use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Formatter};

use rayon::iter::IntoParallelRefIterator;

use message::CasperMsg;
use senders_weight::SendersWeight;
use traits::{Data, Estimate, Zero};
use weight_unit::WeightUnit;

/// Struct that holds the set of the CasperMsgs that justify
/// the current message
/// Works like a Vec
#[derive(Eq, PartialEq, Clone, Default, Hash)]
pub struct Justification<M: CasperMsg>(Vec<M>);

impl<M: CasperMsg> Justification<M> {
    /// Re-exports from Vec wrapping M
    pub fn new() -> Self {
        Justification(Vec::new())
    }

    /// creates a new Justification instance from a Vec of CasperMsg
    /// and a SenderState
    pub fn from_msgs(msgs: Vec<M>, sender_state: &SenderState<M>) -> (Self, SenderState<M>) {
        let mut j = Justification::new();
        let msgs: HashSet<_> = msgs.iter().collect();
        let (_, sender_state) = j.faulty_inserts(msgs, sender_state);
        (j, sender_state)
    }

    pub fn iter(&self) -> std::slice::Iter<M> {
        self.0.iter()
    }

    pub fn par_iter(&self) -> rayon::slice::Iter<M> {
        self.0.par_iter()
    }

    pub fn contains(&self, msg: &M) -> bool {
        self.0.contains(msg)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn insert(&mut self, msg: M) -> bool {
        if self.contains(&msg)
        // || self.iter().any(|m| m.sender() == msg.sender())
        {
            false
        } else {
            self.0.push(msg);
            true
        }
    }

    /// reexport from Estimate impl
    pub fn mk_estimate(
        &self,
        equivocators: &HashSet<M::Sender>,
        senders_weights: &SendersWeight<<M as CasperMsg>::Sender>,
        data: Option<<<M as CasperMsg>::Estimate as Data>::Data>,
    ) -> Result<M::Estimate, &'static str> {
        let latest_msgs = LatestMsgs::from(self);
        let latest_msgs_honest = LatestMsgsHonest::from_latest_msgs(&latest_msgs, equivocators);
        M::Estimate::mk_estimate(&latest_msgs_honest, senders_weights, data)
    }

    // Custom functions

    /// insert msgs to the Justification, accepting up to $thr$ faults by
    /// weight, returns success=true if at least one msg of the set gets
    /// successfully included in the justification
    pub fn faulty_inserts(
        &mut self,
        msgs: HashSet<&M>,
        sender_state: &SenderState<M>,
    ) -> (bool, SenderState<M>) {
        let msgs = sender_state.sort_by_faultweight(msgs);
        // do the actual insertions to the state
        msgs.iter().fold(
            (false, sender_state.clone()),
            |(success, sender_state), &msg| {
                let (success_prime, sender_state_prime) = self.faulty_insert(msg, &sender_state);
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
        let mut sender_state = sender_state.clone();
        let is_equivocation = sender_state.latest_msgs.equivocate(msg);

        let sender = msg.sender();
        let sender_weight = sender_state
            .senders_weights
            .weight(sender)
            .unwrap_or(::std::f64::INFINITY);

        let already_in_equivocators = sender_state.equivocators.contains(sender);

        match (is_equivocation, already_in_equivocators) {
            // if it's already equivocating and listed as such,
            // or not equivocating at all, an insertion can be
            // done without more checks
            (false, _) | (true, true) => {
                let success = self.insert(msg.clone());
                if success {
                    sender_state.latest_msgs.update(msg);
                }
                (success, sender_state)
            }
            // in the other case, we have to check that the threshold is not
            // reached
            (true, false) => {
                if sender_weight + sender_state.state_fault_weight <= sender_state.thr {
                    let success = self.insert(msg.clone());
                    if success {
                        sender_state.latest_msgs.update(msg);
                        if sender_state.equivocators.insert(sender.clone()) {
                            sender_state.state_fault_weight += sender_weight;
                        }
                    }
                    (success, sender_state)
                } else {
                    (false, sender_state)
                }
            }
        }
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
            let sender = msg.sender();
            sender_state.equivocators.insert(sender.clone());
            sender_state
                .senders_weights
                .insert(sender.clone(), WeightUnit::ZERO);
        }
        sender_state.latest_msgs.update(msg);
        let success = self.insert(msg.clone());
        (success, sender_state)
    }
}

impl<M: CasperMsg> Debug for Justification<M> {
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// Set of latest honest messages
pub struct LatestMsgsHonest<M: CasperMsg>(HashSet<M>);

impl<M: CasperMsg> LatestMsgsHonest<M> {
    /// Create an empty set
    fn new() -> Self {
        LatestMsgsHonest(HashSet::new())
    }

    /// Insert message to the set
    fn insert(&mut self, msg: M) -> bool {
        self.0.insert(msg)
    }

    /// Filters the latest messages
    pub fn from_latest_msgs(
        latest_msgs: &LatestMsgs<M>,
        equivocators: &HashSet<M::Sender>,
    ) -> Self {
        latest_msgs
            .iter()
            .filter_map(|(sender, msgs)| {
                if equivocators.contains(sender) || msgs.len() != 1 {
                    None
                } else {
                    msgs.iter().next()
                }
            })
            .fold(LatestMsgsHonest::new(), |mut acc, msg| {
                acc.insert(msg.clone());
                acc
            })
    }

    pub fn iter(&self) -> std::collections::hash_set::Iter<M> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn mk_estimate(
        &self,
        senders_weights: &SendersWeight<<M as CasperMsg>::Sender>,
        data: Option<<<M as CasperMsg>::Estimate as Data>::Data>,
    ) -> Result<M::Estimate, &'static str> {
        M::Estimate::mk_estimate(&self, senders_weights, data)
    }
}

/// Mapping between senders and their latests messages
/// Latest messages from a sender are all their messages that are not
/// in the dependency of another of their messages
#[derive(Eq, PartialEq, Clone, Default, Debug)]
pub struct LatestMsgs<M: CasperMsg>(HashMap<<M as CasperMsg>::Sender, HashSet<M>>);

impl<M: CasperMsg> LatestMsgs<M> {
    /// Create an empty map
    pub fn new() -> Self {
        LatestMsgs(HashMap::new())
    }

    /// insert a new set of messages for a sender
    pub fn insert(&mut self, k: M::Sender, v: HashSet<M>) -> Option<HashSet<M>> {
        self.0.insert(k, v)
    }

    /// checks whether a sender is already contained in the map
    pub fn contains_key(&self, k: &M::Sender) -> bool {
        self.0.contains_key(k)
    }

    /// get a set of messages sent by the sender
    pub fn get(&self, k: &M::Sender) -> Option<&HashSet<M>> {
        self.0.get(k)
    }

    /// get a set of messages sent by the sender as mut
    pub fn get_mut(&mut self, k: &M::Sender) -> Option<&mut HashSet<M>> {
        self.0.get_mut(k)
    }

    pub fn iter(&self) -> std::collections::hash_map::Iter<M::Sender, HashSet<M>> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn keys(&self) -> std::collections::hash_map::Keys<M::Sender, HashSet<M>> {
        self.0.keys()
    }

    pub fn values(&self) -> std::collections::hash_map::Values<'_, M::Sender, HashSet<M>> {
        self.0.values()
    }

    /// update the data structure by adding a new message
    /// return true if new_message is a valid latest message,
    /// aka the first message of a sender or a message that is not
    /// in the justification of the existing latest messages
    pub fn update(&mut self, new_msg: &M) -> bool {
        let sender = new_msg.sender();
        if let Some(latest_msgs_from_sender) = self.get(sender).cloned() {
            latest_msgs_from_sender
                .iter()
                .filter(|&old_msg| new_msg != old_msg)
                .fold(false, |acc, old_msg| {
                    let new_independent_from_old = !new_msg.depends(old_msg);
                    // equivocation, old and new do not depend on each other
                    if new_independent_from_old && !old_msg.depends(new_msg) {
                        self.get_mut(sender)
                            .map(|msgs| msgs.insert(new_msg.clone()))
                            .unwrap_or(false)
                            || acc
                    }
                    // new actually older than old
                    else if new_independent_from_old {
                        false || acc
                    }
                    // new newer than old
                    else {
                        self.get_mut(sender)
                            .map(|msgs| msgs.remove(old_msg) && msgs.insert(new_msg.clone()))
                            .unwrap_or(false)
                            || acc
                    }
                })
        } else {
            // no message found for this sender, so new_msg is the latest
            self.insert(sender.clone(), [new_msg.clone()].iter().cloned().collect());
            true
        }
    }

    /// checks whether msg_new equivocates with latest msgs
    fn equivocate(&self, msg_new: &M) -> bool {
        self.get(msg_new.sender())
            .map(|latest_msgs| latest_msgs.iter().any(|m| m.equivocates(&msg_new)))
            .unwrap_or(false)
    }
}

impl<'z, M: CasperMsg> From<&'z Justification<M>> for LatestMsgs<M> {
    /// extract the latest messages from a justification
    fn from(j: &Justification<M>) -> Self {
        let mut latest_msgs: LatestMsgs<M> = LatestMsgs::new();
        let mut queue: VecDeque<M> = j.iter().cloned().collect();
        while let Some(msg) = queue.pop_front() {
            if latest_msgs.update(&msg) {
                msg.justification()
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
//             j.iter().fold(latest_msgs, |mut acc, m| {
//                 acc.update(m);
//                 recur_func(m.justification(), acc)
//             })
//         }
//         recur_func(j, LatestMsgs::new())
//     }
// }

/// struct that stores the inner state of the sender
#[derive(Debug, Clone)]
pub struct SenderState<M: CasperMsg> {
    /// current state total fault weight
    state_fault_weight: WeightUnit,
    /// fault tolerance threshold
    thr: WeightUnit,
    /// current validator set, mapped to their respective weights
    senders_weights: SendersWeight<M::Sender>,
    /// this sender's last message
    /// TODO: better name?
    my_last_msg: Option<M>,
    latest_msgs: LatestMsgs<M>,
    equivocators: HashSet<M::Sender>,
}

impl<M: CasperMsg> SenderState<M> {
    pub fn new(
        senders_weights: SendersWeight<M::Sender>,
        state_fault_weight: WeightUnit,
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

    pub fn equivocators(&self) -> &HashSet<M::Sender> {
        &self.equivocators
    }

    pub fn senders_weights(&self) -> &SendersWeight<M::Sender> {
        &self.senders_weights
    }

    pub fn my_last_msg(&self) -> &Option<M> {
        &self.my_last_msg
    }

    pub fn latests_msgs(&self) -> &LatestMsgs<M> {
        &self.latest_msgs
    }

    pub fn latests_msgs_as_mut(&mut self) -> &mut LatestMsgs<M> {
        &mut self.latest_msgs
    }

    /// get msgs and fault weight overhead and equivocators overhead sorted
    /// by fault weight overhead against the current sender_state
    fn sort_by_faultweight<'z>(&self, msgs: HashSet<&'z M>) -> Vec<&'z M> {
        let mut msgs_sorted_by_faultw: Vec<_> = msgs
            .iter()
            .filter_map(|&msg| {
                // equivocations in relation to state
                let sender = msg.sender();
                if !self.equivocators.contains(sender) && self.latest_msgs.equivocate(msg) {
                    self.senders_weights.weight(sender).map(|w| (msg, w)).ok()
                } else {
                    Some((msg, WeightUnit::ZERO))
                }
            })
            .collect();

        let _ = msgs_sorted_by_faultw.sort_unstable_by(|(m0, w0), (m1, w1)| {
            w0.partial_cmp(w1).unwrap_or(m0.id().cmp(m1.id())) // tie breaker
        });

        // return a Vec<CasperMsg>
        msgs_sorted_by_faultw
            .iter()
            .map(|(m, _)| m)
            .cloned()
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use example::vote_count::VoteCount;
    use message::Message;

    #[test]
    fn faulty_inserts_sorted() {
        let senders_weights =
            SendersWeight::new([(0, 1.0), (1, 2.0), (2, 3.0)].iter().cloned().collect());

        let v0 = &VoteCount::create_vote_msg(0, false);
        let v0_prime = &VoteCount::create_vote_msg(0, true);
        let v1 = &VoteCount::create_vote_msg(1, true);
        let v1_prime = &VoteCount::create_vote_msg(1, false);
        let v2 = &VoteCount::create_vote_msg(2, true);
        let v2_prime = &VoteCount::create_vote_msg(2, false);
        let mut sender_state = SenderState {
            senders_weights: senders_weights.clone(),
            state_fault_weight: 0.0,
            my_last_msg: None,
            thr: 3.0,
            equivocators: HashSet::new(),
            latest_msgs: LatestMsgs::new(),
        };
        let mut j = Justification::new();
        let _ = sender_state.latest_msgs.update(v0);
        let _ = sender_state.latest_msgs.update(v1);
        let _ = sender_state.latest_msgs.update(v2);
        let sorted_msgs = sender_state
            .sort_by_faultweight(vec![v2_prime, v1_prime, v0_prime].iter().cloned().collect());
        let (_, sender_state) =
            sorted_msgs
                .iter()
                .fold((false, sender_state), |(success, sender_state), &m| {
                    let (s, w) = j.faulty_insert(m, &sender_state);
                    (s || success, w)
                });
        assert!(j.contains(v0_prime));
        assert!(j.contains(v1_prime));
        assert!(!j.contains(v2_prime));
        assert_eq!(sender_state.state_fault_weight, 3.0);
    }
    #[test]
    fn faulty_inserts() {
        let senders_weights =
            SendersWeight::new([(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect());
        let v0 = &VoteCount::create_vote_msg(0, false);
        let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = &VoteCount::create_vote_msg(1, true);
        let mut j0 = Justification::new();

        let sender_state = SenderState {
            senders_weights: senders_weights.clone(),
            state_fault_weight: (0.0),
            my_last_msg: None,
            thr: 0.0,
            equivocators: HashSet::new(),
            latest_msgs: LatestMsgs::new(),
        };

        let (success, sender_state) =
            j0.faulty_inserts([v0].iter().cloned().collect(), &sender_state);
        assert!(success);

        let (m0, _weights) =
            &Message::from_msgs(0, vec![v0], &sender_state, None as Option<VoteCount>).unwrap();

        // let m0 = &Message::new(0, justification, estimate);
        let mut j1 = Justification::new();
        let (success, sender_state) =
            j1.faulty_inserts(vec![v1].iter().cloned().collect(), &sender_state);
        assert!(success);

        let (success, sender_state) =
            j1.faulty_inserts(vec![m0].iter().cloned().collect(), &sender_state);
        assert!(success);

        let (success, sender_state) = j1.faulty_insert(v0_prime, &sender_state);
        assert!(
            !success,
            "$v0_prime$ should conflict with $v0$ through $m0$, and we should reject as our fault tolerance thr is zero"
        );

        let (success, _) = j1.clone().faulty_insert(
            v0_prime,
            &SenderState {
                senders_weights: senders_weights.clone(),
                state_fault_weight: (0.0),
                my_last_msg: None,
                thr: 1.0,
                equivocators: HashSet::new(),
                latest_msgs: LatestMsgs::new(),
            },
        );
        assert!(success,
            "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set"
        );

        let (_, sender_state2) = j1.clone().faulty_insert(
            v0_prime,
            &SenderState {
                thr: 1.0,
                ..sender_state.clone()
            },
        );
        assert_eq!(
            sender_state2.state_fault_weight, 1.0,
            "$v0_prime$ conflicts with $v0$ through $m0$, but we should accept this fault as it doesnt cross the fault threshold for the set, and thus the state_fault_weight should be incremented to 1.0"
        );

        let (success, _) = j1.clone().faulty_insert(
            v0_prime,
            &SenderState {
                state_fault_weight: (0.1),
                thr: 1.0,
                ..sender_state.clone()
            },
        );
        assert!(!success,
            "$v0_prime$ conflicts with $v0$ through $m0$, and we should not accept this fault as the fault threshold gets crossed for the set"
        );

        let (_, sender_state2) = j1.clone().faulty_insert(
            v0_prime,
            &SenderState {
                state_fault_weight: (0.1),
                thr: 1.0,
                ..sender_state.clone()
            },
        );
        assert_eq!(sender_state2.state_fault_weight, 0.1,
            "$v0_prime$ conflicts with $v0$ through $m0$, and we should NOT accept this fault as the fault threshold gets crossed for the set, and thus the state_fault_weight should not be incremented"
        );

        let (success, _) = j1.clone().faulty_insert(
            v0_prime,
            &SenderState {
                state_fault_weight: (1.0),
                thr: 2.0,
                ..sender_state.clone()
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
                state_fault_weight: 1.0,
                thr: 2.0,
                ..sender_state.clone()
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
                state_fault_weight: (1.0),
                my_last_msg: None,
                thr: 2.0,
                equivocators: HashSet::new(),
                latest_msgs: LatestMsgs::new(),
            },
        );
        assert_eq!(
                sender_state.state_fault_weight,
            1.0,
            "$v0_prime$ conflict with $v0$ through $m0$, but we should NOT accept this fault as we can't know the weight of the sender, which could be Infinity, and thus the state_fault_weight should be unchanged"
        );
    }
}
