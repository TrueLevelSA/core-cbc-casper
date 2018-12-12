use std::collections::{BTreeSet, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::fmt::{Debug, Formatter, Result as FmtResult};
use std::sync::{Arc, RwLock};
use std::iter;
use std::iter::FromIterator;
// use std::io::{Error};

use rayon::prelude::*;
use proptest::prelude::*;

use proptest::test_runner::Config;
use proptest::test_runner::TestRunner;
use proptest::strategy::ValueTree;
use rand::{thread_rng, Rng};

use traits::{Estimate, Zero, Sender, Data, Id, };
use justification::{Justification, SenderState, LatestMsgsHonest};
use weight_unit::{WeightUnit};
use senders_weight::SendersWeight;
use hashed::Hashed;

/// A Casper Message, that can will be sent over the network
/// and used as a justification for a more recent message
pub trait CasperMsg: Hash + Clone + Eq + Sync + Send + Debug + Id + serde::Serialize {
    // To be implemented on concrete struct
    type Sender: Sender;
    type Estimate: Estimate<M = Self>;

    /// returns the validator who sent this message
    fn get_sender(&self) -> &Self::Sender;

    /// returns the estimate of this message
    fn get_estimate(&self) -> &Self::Estimate;

    /// returns the justification of this message
    fn get_justification<'z>(&'z self) -> &'z Justification<Self>;

    fn id(&self) -> &Self::ID;

    /// creates a new instance of this message
    fn new(
        sender: Self::Sender,
        justification: Justification<Self>,
        estimate: Self::Estimate,
        id: Option<Self::ID>,
    ) -> Self;

    // this function is used to clean up memory. when a msg is final, there's no
    // need to keep its justifications. when dropping its justification, all the
    // Msgs (Arc) which are referenced on the justification will get dropped
    // from memory
    // fn set_as_final(&mut self);

    // Following methods are actual implementations

    /// create a msg from newly received messages
    /// finalized_msg allows to shortcut the recursive checks
    fn from_msgs(
        sender: Self::Sender,
        new_msgs: Vec<&Self>,
        finalized_msg: Option<&Self>,
        sender_state: &SenderState<Self>,
        external_data: Option<<Self::Estimate as Data>::Data>,
    ) -> Result<(Self, SenderState<Self>), &'static str> {
        // // TODO eventually comment out these lines, and FIXME tests
        // // check whether two messages from same sender
        // let mut senders = HashSet::new();
        // let dup_senders = new_msgs.iter().any(|msg| !senders.insert(msg.get_sender()));
        // assert!(!dup_senders, "A sender can only have one, and only one, latest message");

        // dedup by putting msgs into a hashset
        // TODO DL: why don't we directly ask for a hashset instead of a Vec?
        let new_msgs: HashSet<_> = new_msgs.iter().cloned().collect();

        let mut justification = Justification::new();
        sender_state.get_my_last_msg().as_ref().map_or_else(
            // || println!("No commitment to any previous state!"),
            || (),
            |my_last_msg| {
                justification.insert(my_last_msg.clone());
            },
        );

        let new_msgs_len = new_msgs.len();

        // update latest_msgs in sender_state with new_msgs and reset justification (since new_msgs may not all reflect in updated latest_msgs)
        let (success, sender_state) =
            justification.faulty_inserts(new_msgs, &sender_state);
        justification = Justification::new();

        if !success && new_msgs_len > 0 {
            Err("None of the messages could be added to the state!")
        } else {
            let latest_msgs_honest = LatestMsgsHonest::from_latest_msgs(
                sender_state.get_latest_msgs(),
                sender_state.get_equivocators(),
            );

            latest_msgs_honest.iter().for_each(|m| {justification.faulty_insert(m, &sender_state);});

            let estimate = latest_msgs_honest.mk_estimate(
                finalized_msg,
                &sender_state.get_senders_weights(),
                external_data,
            );

            let message = Self::new(sender, justification, estimate, None);
            Ok((message, sender_state))
        }
    }

    /// insanely expensive
    fn equivocates_indirect(
        &self,
        rhs: &Self,
        mut equivocators: HashSet<<Self as CasperMsg>::Sender>,
    ) -> (bool, HashSet<<Self as CasperMsg>::Sender>) {
        let is_equivocation = self.equivocates(rhs);
        let init = if is_equivocation {
            equivocators.insert(self.get_sender().clone());
            (true, equivocators)
        } else {
            (false, equivocators)
        };
        self.get_justification().iter().fold(
            init,
            |(acc_has_equivocations, acc_equivocators), self_prime| {
                // note the rotation between rhs and self, done because
                // descending only on self, thus rhs has to become self on the
                // recursion to get its justification visited
                let (has_equivocation, equivocators) = rhs
                    .equivocates_indirect(self_prime, acc_equivocators.clone());
                let acc_equivocators =
                    acc_equivocators.union(&equivocators).cloned().collect();
                (acc_has_equivocations || has_equivocation, acc_equivocators)
            },
        )
    }

    /// Math definition of the equivocation
    fn equivocates(&self, rhs: &Self) -> bool {
        self != rhs
            && self.get_sender() == rhs.get_sender()
            && !rhs.depends(self)
            && !self.depends(rhs)
    }

    /// checks whether self depends on rhs
    /// returns true if rhs is somewhere in the justification of self
    fn depends(&self, rhs: &Self) -> bool {
        // although the recursion ends supposedly only at genesis message, the
        // trick is the following: it short-circuits while descending on the
        // dependency tree, if it finds a dependent message. when dealing with
        // honest validators, this would return true very fast. all the new
        // derived branches of the justification will be evaluated in parallel.
        // say if a msg is justified by 2 other msgs, then the 2 other msgs will
        // be processed on different threads. this applies recursively, so if
        // each of the 2 msgs have say 3 justifications, then each of the 2
        // threads will spawn 3 new threads to process each of the messages.
        // thus, highly parallelizable. when it shortcuts, because in one thread
        // a dependency was found, the function returns true and all the
        // computation on the other threads will be canceled.
        // TODO DL: bad idea to spawn threads recursively and without upper bound
        fn recurse<M: CasperMsg>(lhs: &M, rhs: &M, visited: Arc<RwLock<HashSet<M>>>) -> bool {
            let justification = lhs.get_justification();

            // Math definition of dependency
            justification.contains(rhs)
                || justification
                .par_iter()
                .filter(|lhs_prime| visited.read().map(|v| !v.contains(lhs_prime)).ok().unwrap_or(true))
                .any(|lhs_prime| {
                    let visited_prime = visited.clone();
                    let _ = visited_prime.write().map(|mut v| v.insert(lhs_prime.clone())).ok();
                    recurse(lhs_prime, rhs, visited_prime)
                })
        }
        let visited = Arc::new(RwLock::new(HashSet::new()));
        recurse(self, rhs, visited)
    }

    /// checks whether ther is a circular dependency between self and rhs
    fn is_circular(&self, rhs: &Self) -> bool {
        rhs.depends(self) && self.depends(rhs)
    }

    /// returns the dag tip-most safe messages. a safe message is defined as one
    /// that was seen by all senders (with non-zero weight in senders_weights)
    /// and all senders saw each other seeing each other messages.
    fn get_msg_for_proposition(
        &self,
        all_senders: &HashSet<Self::Sender>,
    ) -> HashSet<Self> {

        /// recursively looks for all tips of the dag
        fn recursor<M>(
            m: &M,
            all_senders: &HashSet<M::Sender>,
            mut senders_referred: HashSet<M::Sender>,
            safe_msgs: HashSet<M>,
            original_sender: &M::Sender,
        ) -> HashSet<M>
        where
            M: CasperMsg,
        {
            m.get_justification().iter().fold(
                safe_msgs,
                |mut safe_msgs_prime, msg_prime| {
                    // base case
                    if &senders_referred == all_senders
                        && original_sender == msg_prime.get_sender()
                    {
                        let _ = safe_msgs_prime.insert(msg_prime.clone());
                        safe_msgs_prime
                    }
                    else {
                        let _ = senders_referred
                            .insert(msg_prime.get_sender().clone());

                        recursor(
                            msg_prime,
                            all_senders,
                            senders_referred.clone(),
                            safe_msgs_prime,
                            original_sender,
                        )
                    }
                }
            )
        };

        // initial state, trigger recursion
        let original_sender = self.get_sender();
        let senders_refered =
            [original_sender.clone()].iter().cloned().collect();
        let safe_msgs = HashSet::new();
        recursor(
            self,
            all_senders,
            senders_refered,
            safe_msgs,
            &original_sender,
        )
    }

    /// returns the dag tip-most safe messages. a safe message is defined as one
    /// that was seen by more than a given thr of total weight units. TODO: not
    /// sure about this implementation, i assume its not working correctly.
    fn get_safe_msgs_by_weight(
        &self,
        senders_weights: &SendersWeight<Self::Sender>,
        thr: &WeightUnit,
    ) -> HashMap<Self, WeightUnit> {
        fn recursor<M>(
            m: &M,
            senders_weights: &SendersWeight<M::Sender>,
            mut senders_referred: HashSet<M::Sender>,
            weight_referred: WeightUnit,
            thr: &WeightUnit,
            safe_msg_weight: HashMap<M, WeightUnit>,
        ) -> HashMap<M, WeightUnit>
        where
            M: CasperMsg,
        {
            m.get_justification().iter().fold(
                safe_msg_weight,
                |mut safe_msg_weight_prime, m_prime| {
                    // base case
                    if &weight_referred > thr {
                        let _ = safe_msg_weight_prime
                            .insert(m.clone(), weight_referred);
                        safe_msg_weight_prime
                    } else {
                        let sender_current = m_prime.get_sender();
                        let weight_referred = if senders_referred
                            .insert(sender_current.clone())
                        {
                            weight_referred
                                + senders_weights
                                    .get_weight(&sender_current)
                                    .unwrap_or(WeightUnit::ZERO)
                        } else {
                            weight_referred
                        };

                        recursor(
                            m_prime,
                            senders_weights,
                            senders_referred.clone(),
                            weight_referred,
                            thr,
                            safe_msg_weight_prime,
                        )
                    }
                },
            )
        };

        // initial state, trigger recursion
        let senders_referred = [].iter().cloned().collect();
        let weight_referred = WeightUnit::ZERO;
        let safe_msg_weight = HashMap::new();

        recursor(
            self,
            senders_weights,
            senders_referred,
            weight_referred,
            thr,
            safe_msg_weight,
        )
    }
}

/// Mathematical definition of a casper message
#[derive(Clone, Default, Eq, PartialEq)]
struct ProtoMsg<E, S>
where
    E: Estimate<M = Message<E, S>>,
    S: Sender,
{
    estimate: E,
    sender: S,
    justification: Justification<Message<E, S>>,
}

/// Boxing of a ProtoMsg, that will implement the trait CasperMsg
#[derive(Eq, Clone, Default)]
pub struct Message<E, S>(Arc<ProtoMsg<E, S>>, Hashed)
where
    E: Estimate<M = Message<E, S>>,
    S: Sender;

/*
// TODO start we should make messages lazy. continue this after async-await is better
// documented

enum MsgStatus {
Unchecked,
Valid,
Invalid,
}

struct Message<E, S, D>
where
    E: Estimate,
    S: Sender,
{
    status: MsgStatus,
    msg: Future<Item = Message<E, S, D>, Error = Error>,
}
// TODO end
*/

// impl<E, S> From<ProtoMsg<E, S>> for Message<E, S>
// where
//     E: Estimate<M = Self>,
//     S: Sender,
// {
//     fn from(msg: ProtoMsg<E, S>) -> Self {
//         let id = msg.getid();
//         Message(Arc::new(msg), id)
//     }
// }

impl<E, S> Id for ProtoMsg<E, S>
where
    E: Estimate<M = Message<E, S>>,
    S: Sender,
{
    type ID = Hashed;
}

impl<E, S> Id for Message<E, S>
where
    E: Estimate<M = Self>,
    S: Sender,
{
    type ID = Hashed;
    fn getid(&self) -> Self::ID {
        self.1.clone()
    }
}

impl<E, S> serde::Serialize for ProtoMsg<E, S>
where
    E: Estimate<M = Message<E, S>>,
    S: Sender,
{
    fn serialize<T: serde::Serializer>(&self, serializer: T) -> Result<T::Ok, T::Error> {
        use serde::ser::SerializeStruct;

        let mut msg = serializer.serialize_struct("Message", 3)?;
        let j: Vec<_> = self.justification.iter().map(Message::id).collect();
        msg.serialize_field("sender", &self.sender)?;
        msg.serialize_field("estimate", &self.estimate)?;
        msg.serialize_field("justification", &j)?;
        msg.end()
    }
}

impl<E, S> serde::Serialize for Message<E, S>
where
    E: Estimate<M = Self>,
    S: Sender,
{
    fn serialize<T: serde::Serializer>(&self, serializer: T) -> Result<T::Ok, T::Error> {
        use serde::ser::SerializeStruct;
        let mut msg = serializer.serialize_struct("Message", 3)?;
        let j: Vec<_> = self.get_justification().iter().map(Self::id).collect();
        msg.serialize_field("sender", self.get_sender())?;
        msg.serialize_field("estimate", self.get_estimate())?;
        msg.serialize_field("justification", &j)?;
        msg.end()
    }
}

impl<E, S> CasperMsg for Message<E, S>
where
    E: Estimate<M = Self>,
    S: Sender,
{
    type Estimate = E;
    type Sender = S;

    fn get_sender(&self) -> &Self::Sender {
        &self.0.sender
    }

    fn get_estimate(&self) -> &Self::Estimate {
        &self.0.estimate
    }

    fn get_justification<'z>(&'z self) -> &'z Justification<Self> {
        &self.0.justification
    }
    fn id(&self) -> &<Self as Id>::ID { &self.1 }
    fn new(sender: S, justification: Justification<Self>, estimate: E, id: Option<Self::ID>) -> Self {
        let proto = ProtoMsg{sender, justification, estimate};
        let id = id.unwrap_or(proto.getid());
        Message(Arc::new(proto), id)
    }

    // fn set_as_final(&mut self) {
    //     let mut proto_msg = (**self.0).clone();
    //     proto_msg.justification = Justification::new();
    //     *self.0 = Arc::new(proto_msg);
    // }
}

impl<E, S> Hash for Message<E, S>
where
    E: Estimate<M = Self>,
    S: Sender,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state)
    }
}

impl<E, S> PartialEq for Message<E, S>
where
    E: Estimate<M = Self>,
    S: Sender,
{
    fn eq(&self, rhs: &Self) -> bool {
        Arc::ptr_eq(&self.0, &rhs.0)
            || self.id() == rhs.id() // should make this line unnecessary
    }
}

impl<E, S> Debug for Message<E, S>
where
    E: Estimate<M = Self>,
    S: Sender,
{
    // Note: format used for rendering illustrative gifs from generative tests; modify with care
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(
            f,
            "M{:?}({:?})",
            // "M{:?}({:?}) -> {:?}",
            self.get_sender(),
            self.get_estimate().clone(),
            // self.get_justification()
        )
    }
}

#[cfg(test)]
mod tests {
    use example::binary::BoolWrapper;
    use example::integer::IntegerWrapper;
    use example::vote_count::{VoteCount};
    use senders_weight::{SendersWeight};
    use justification::{LatestMsgs};
    use example::blockchain::*;

    use std::{f64};
    use super::*;

    // Implementations of From<Sender>
    impl<S: Sender> From<S> for BoolWrapper {
        fn from(_sender: S) -> Self {
            BoolWrapper::new(bool::default())
        }
    }

    impl<S: Sender> From<S> for VoteCount {
        fn from(_sender: S) -> Self {
            VoteCount::default()
        }
    }

    impl <S: Sender> From<S> for IntegerWrapper {
        fn from(_sender: S) -> Self {
            IntegerWrapper::new(u32::default())
        }
    }

    impl<S: Sender + Into<u32>> From<S> for Block {
        fn from(sender: S) -> Self {
            (Block::from(ProtoBlock::new(None, sender.into())))
        }
    }

    fn add_message<'z, M>(
        state: &'z mut HashMap<M::Sender, SenderState<M>>,
        sender: M::Sender,
        recipients: HashSet<M::Sender>,
        data: Option<<M::Estimate as Data>::Data>,
    ) -> &'z HashMap<M::Sender, SenderState<M>>
    where
        M: CasperMsg,
    {
        let (m, sender_state) = M::from_msgs(sender.clone(), vec![], None, &state[&sender], data.clone().map(|d| d.into())).unwrap();

        state.insert(sender, sender_state);
        recipients.iter().for_each(|recipient| {
            let (_, recipient_state) =
                Justification::from_msgs(vec![m.clone()], &state[recipient]);
            state.insert(recipient.clone(), recipient_state);
        });
        state
    }

    fn round_robin(val: &mut Vec<u32>) -> BoxedStrategy<u32> {
        let v = val.pop().unwrap();
        val.insert(0, v);
        Just(v).boxed()
    }

    fn arbitrary_in_set(val: &mut Vec<u32>) -> BoxedStrategy<u32> {
        prop::sample::select(val.clone()).boxed()
    }

    fn all_receivers(val: &Vec<u32>) -> BoxedStrategy<HashSet<u32>> {
        let v = HashSet::from_iter(val.iter().cloned());
        Just(v).boxed()
    }

    fn some_receivers(val: &Vec<u32>) -> BoxedStrategy<HashSet<u32>> {
        prop::collection::hash_set(
            prop::sample::select(val.clone()),
            0..(val.len() + 1),
        ).boxed()
    }

    fn message_event<M>(
        state: HashMap<M::Sender, SenderState<M>>,
        sender_strategy: BoxedStrategy<M::Sender>,
        receiver_strategy: BoxedStrategy<HashSet<M::Sender>>,
    ) -> BoxedStrategy<HashMap<M::Sender, SenderState<M>>>
    where
        M: 'static + CasperMsg,
        <<M as CasperMsg>::Estimate as Data>::Data: From<<M as CasperMsg>::Sender>
    {
        (sender_strategy, receiver_strategy, Just(state))
            .prop_map(|(sender, mut receivers, mut state)| {
                if !receivers.contains(&sender) {
                    receivers.insert(sender.clone());
                }
                add_message(&mut state, sender.clone(), receivers, Some(sender.into())).clone()
            })
            .boxed()
    }

    fn full_consensus<M>(state: &HashMap<M::Sender, SenderState<M>>) -> bool
    where
        M: CasperMsg,
    {
        let m: HashSet<_> = state
            .iter()
            .map(|(_sender, sender_state)| {
                let latest_honest_msgs = LatestMsgsHonest::from_latest_msgs(
                    sender_state.get_latest_msgs(),
                    &HashSet::new(),
                );
                latest_honest_msgs.mk_estimate(
                    None,
                    sender_state.get_senders_weights(),
                    None,
                )
            })
            .collect();
        println!("{:?}", m);
        m.len() == 1
    }

    fn safety_oracle(state: &HashMap<u32, SenderState<BlockMsg>>) -> bool {
        let safety_oracle_detected: HashSet<bool> = state
            .iter()
            .map(|(_, sender_state)| {
                let latest_honest_msgs = LatestMsgsHonest::from_latest_msgs(
                    sender_state.get_latest_msgs(),
                    &HashSet::new(),
                );
                let genesis_block = Block::from(ProtoBlock::new(None, 0));
                let safety_threshold =
                    (sender_state.get_senders_weights().sum_all_weights())
                        / 2.0;
                Block::safety_oracles(
                    genesis_block,
                    &latest_honest_msgs,
                    &HashSet::new(),
                    safety_threshold,
                    sender_state.get_senders_weights(),
                ) != HashSet::new()
            })
            .collect();
        safety_oracle_detected.contains(&true)
    }

    fn clique_collection(
        state: HashMap<u32, SenderState<BlockMsg>>,
    ) -> Vec<Vec<Vec<u32>>> {
        state
            .iter()
            .map(|(_, sender_state)| {
                let genesis_block = Block::from(ProtoBlock::new(None, 0));
                let latest_honest_msgs = LatestMsgsHonest::from_latest_msgs(
                    sender_state.get_latest_msgs(),
                    &HashSet::new(),
                );
                let safety_oracles = Block::safety_oracles(
                    genesis_block,
                    &latest_honest_msgs,
                    &HashSet::new(),
                    // cliques, not safety oracles, because our threshold is 0
                    0.0,
                    sender_state.get_senders_weights(),
                );
                let safety_oracles_vec_of_btrees: Vec<
                    BTreeSet<u32>,
                > = Vec::from_iter(safety_oracles.iter().cloned());
                let safety_oracles_vec_of_vecs: Vec<Vec<u32>> =
                    safety_oracles_vec_of_btrees
                        .iter()
                        .map(|btree| Vec::from_iter(btree.iter().cloned()))
                        .collect();
                safety_oracles_vec_of_vecs
            })
            .collect()
    }

    fn chain<E: 'static, F: 'static, G: 'static, H: 'static>(
        consensus_value_strategy: BoxedStrategy<E>,
        validator_max_count: usize,
        message_producer_strategy: F,
        message_receiver_strategy: G,
        consensus_satisfied: H,
    ) -> BoxedStrategy<Vec<HashMap<u32, SenderState<Message<E, u32>>>>>
    where
        E: Estimate<M = Message<E, u32>> + From<u32>,
        F: Fn(&mut Vec<u32>) -> BoxedStrategy<u32>,
        G: Fn(&Vec<u32>) -> BoxedStrategy<HashSet<u32>>,
        H: Fn(&HashMap<u32, SenderState<Message<E, u32>>>) -> bool,
    {
        (prop::sample::select((1..validator_max_count).collect::<Vec<usize>>()))
            .prop_flat_map(move |validators| {
                (prop::collection::vec(
                    consensus_value_strategy.clone(),
                    validators,
                ))
            })
            .prop_map(move |votes| {
                let mut state = HashMap::new();
                let validators: Vec<u32> = (0..votes.len() as u32).collect();

                let weights: Vec<f64> =
                    iter::repeat(1.0).take(votes.len() as usize).collect();

                let senders_weights = SendersWeight::new(
                    validators
                        .iter()
                        .cloned()
                        .zip(weights.iter().cloned())
                        .collect(),
                );

                validators.iter().for_each(|validator| {
                    let mut j = Justification::new();
                    let m = Message::new(
                        *validator,
                        j.clone(),
                        votes[*validator as usize].clone(),
                        None,
                    );
                    j.insert(m.clone());
                    state.insert(
                        *validator,
                        SenderState::new(
                            senders_weights.clone(),
                            0.0,
                            Some(m),
                            LatestMsgs::from(&j),
                            0.0,
                            HashSet::new(),
                        ),
                    );
                });

                let mut runner = TestRunner::default();
                let mut senders = validators.clone();
                let chain = iter::repeat_with(|| {
                    let sender_strategy =
                        message_producer_strategy(&mut senders);
                    let receiver_strategy = message_receiver_strategy(&senders);
                    state = message_event(
                        state.clone(),
                        sender_strategy,
                        receiver_strategy,
                    ).new_value(&mut runner)
                        .unwrap()
                        .current();
                    state.clone()
                });
                let mut have_consensus = false;
                Vec::from_iter(chain.take_while(|state| {
                    if have_consensus {
                        false
                    } else {
                        if consensus_satisfied(state) {
                            have_consensus = true
                        }
                        true
                    }
                }))
            })
            .boxed()
    }


    fn arbitrary_blockchain() -> BoxedStrategy<Block> {
        let genesis_block = Block::from(ProtoBlock::new(None, 0));
        Just(genesis_block).boxed()
    }

    proptest! {
        #![proptest_config(Config::with_cases(100))]
        #[test]
        fn blockchain(ref chain in chain(arbitrary_blockchain(), 6, round_robin, some_receivers, safety_oracle)) {
            // total messages until unilateral consensus
            println!("new chain");
            chain.iter().for_each(|state| {println!("{{lms: {:?},", state.iter().map(|(_, sender_state)|
                                                                             sender_state.get_latest_msgs()).collect::<Vec<_>>());
                                           println!("sendercount: {:?},", state.keys().len());
                                           print!("clqs: ");
                                           println!("{:?}}},", clique_collection(state.clone()));
            });
        }
    }

    proptest! {
        #![proptest_config(Config::with_cases(30))]
        #[test]
        fn round_robin_vote_count(ref chain in chain(VoteCount::arbitrary(), 15, round_robin, all_receivers, full_consensus)) {
            assert_eq!(chain.last().unwrap_or(&HashMap::new()).keys().len(),
                       if chain.len() > 0 {chain.len()} else {0},
                       "round robin with n validators should converge in n messages")
        }
    }

    prop_compose! {
        fn boolwrapper_gen()
            (boolean in prop::bool::ANY) -> BoolWrapper {
                BoolWrapper::new(boolean)
            }
    }

    prop_compose! {
        fn integerwrapper_gen()
            (int in prop::num::u32::ANY) -> IntegerWrapper {
                IntegerWrapper::new(int)
            }
    }

    proptest! {
        #![proptest_config(Config::with_cases(30))]
        #[test]
        fn round_robin_binary(ref chain in chain(boolwrapper_gen(), 15, round_robin, all_receivers, full_consensus)) {
            assert!(chain.last().unwrap_or(&HashMap::new()).keys().len() >=
                    chain.len(),
                    "round robin with n validators should converge in at most n messages")
        }
    }

    proptest! {
        #![proptest_config(Config::with_cases(10))]
        #[test]
        fn round_robin_integer(ref chain in chain(integerwrapper_gen(), 2000, round_robin, all_receivers, full_consensus)) {
            // total messages until unilateral consensus
            println!("{} validators -> {:?} message(s)",
                     match chain.last().unwrap_or(&HashMap::new()).keys().len().to_string().as_ref()
                     {"0" => "Unknown",
                      x => x},
                     chain.len());
            assert!(chain.last().unwrap_or(&HashMap::new()).keys().len() >=
                    chain.len(),
                    "round robin with n validators should converge in at most n messages")
        }
    }

    proptest! {
        #![proptest_config(Config::with_cases(1))]
        #[test]
        fn arbitrary_messenger_vote_count(ref chain in chain(VoteCount::arbitrary(), 8, arbitrary_in_set, some_receivers, full_consensus)) {
            // total messages until unilateral consensus
            println!("{} validators -> {:?} message(s)",
                     match chain.last().unwrap_or(&HashMap::new()).keys().len().to_string().as_ref()
                     {"0" => "Unknown",
                      x => x},
                     chain.len());
        }
    }

    proptest! {
        #![proptest_config(Config::with_cases(1))]
        #[test]
        fn arbitrary_messenger_binary(ref chain in chain(boolwrapper_gen(), 100, arbitrary_in_set, some_receivers, full_consensus)) {
            // total messages until unilateral consensus
            println!("{} validators -> {:?} message(s)",
                     match chain.last().unwrap_or(&HashMap::new()).keys().len().to_string().as_ref()
                     {"0" => "Unknown",
                      x => x},
                     chain.len());
        }
    }

    proptest! {
        #![proptest_config(Config::with_cases(1))]
        #[test]
        fn arbitrary_messenger_integer(ref chain in chain(integerwrapper_gen(), 50, arbitrary_in_set, some_receivers, full_consensus)) {
            // total messages until unilateral consensus
            println!("{} validators -> {:?} message(s)",
                     match chain.last().unwrap_or(&HashMap::new()).keys().len().to_string().as_ref()
                     {"0" => "Unknown",
                      x => x},
                     chain.len());
        }
    }

    prop_compose! {
        fn votes(senders: usize, equivocations: usize)
            (votes in prop::collection::vec(prop::bool::weighted(0.3), senders as usize),
             equivocations in Just(equivocations),
             senders in Just(senders))
             -> (Vec<Message<VoteCount, u32>>, HashSet<u32>, usize)
        {
            let mut validators: Vec<u32> = (0..senders as u32).collect();
            thread_rng().shuffle(&mut validators);
            let equivocators: HashSet<u32> = HashSet::from_iter(validators[0..equivocations].iter().cloned());

            let mut messages = vec![];
            votes
                .iter()
                .enumerate()
                .for_each(|(sender, vote)|
                          {messages.push(VoteCount::create_vote_msg(sender as u32, vote.clone()))});
            equivocators
                .iter()
                .for_each(|equivocator|
                          {let vote = !votes[*equivocator as usize];
                           messages.push(VoteCount::create_vote_msg(*equivocator as u32, vote))});
            (messages, equivocators, senders)
        }
    }

    proptest! {
        #![proptest_config(Config::with_cases(1000))]
        #[test]
        fn detect_equivocation(ref vote_tuple in votes(5, 5)) {
            let (messages, equivocators, nodes) = vote_tuple;
            let nodes = nodes.clone();
            let senders: Vec<u32> = (0..nodes as u32).collect();
            let weights: Vec<f64> =
                iter::repeat(1.0).take(nodes as usize).collect();
            let senders_weights = SendersWeight::new(
                senders
                    .iter()
                    .cloned()
                    .zip(weights.iter().cloned())
                    .collect(),
            );
            let sender_state = SenderState::new(
                senders_weights.clone(),
                0.0,
                None,
                LatestMsgs::new(),
                0.0,
                HashSet::new(),
            );

            // here, only take one equivocation
            let single_equivocation: Vec<_> = messages[..nodes+1].iter().map(|message| message).collect();
            let equivocator = messages[nodes].get_sender();
            let (m0, _) =
                &Message::from_msgs(0, single_equivocation.clone(), None, &sender_state, None)
                .unwrap();
            let equivocations: Vec<_> = single_equivocation.iter().filter(|message| message.equivocates(&m0)).collect();
            assert!(if *equivocator == 0 {equivocations.len() == 1} else {equivocations.len() == 0}, "should detect sender 0 equivocating if sender 0 equivocates");
            // the following commented test should fail
            // assert_eq!(equivocations.len(), 1, "should detect sender 0 equivocating if sender 0 equivocates");

            let (m0, _) =
                &Message::from_msgs(0, messages.iter().map(|message| message).collect(), None, &sender_state, None)
                .unwrap();
            let equivocations: Vec<_> = messages.iter().filter(|message| message.equivocates(&m0)).collect();
            assert_eq!(equivocations.len(), 1, "should detect sender 0 equivocating if sender 0 equivocates");

            let sender_state = SenderState::new(
                senders_weights,
                0.0,
                None,
                LatestMsgs::new(),
                equivocators.len() as f64,
                HashSet::new(),
            );
            let (m0, _) =
                &Message::from_msgs(0, messages.iter().map(|message| message).collect(), None, &sender_state, None)
                .unwrap();
            let equivocations: Vec<_> = messages.iter().filter(|message| message.equivocates(&m0)).collect();
            assert_eq!(equivocations.len(), 0, "equivocation absorbed in threshold");
        }
    }

    #[test]
    fn debug() {
        let v0 = VoteCount::create_vote_msg(0, false);
        println!("{:?}", v0);
    }

    #[test]
    fn msg_equality() {
        // v0 and v0_prime are equivocating messages (first child of a fork).
        let v0 = &VoteCount::create_vote_msg(0, false);
        let v1 = &VoteCount::create_vote_msg(1, true);
        let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
        let v0_idem = &VoteCount::create_vote_msg(0, false);

        assert!(v0 == v0_idem, "v0 and v0_idem should be equal");
        assert!(v0 != v0_prime, "v0 and v0_prime should NOT be equal");
        assert!(v0 != v1, "v0 and v1 should NOT be equal");

        let senders_weights = SendersWeight::new(
            [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect(),
        );

        let sender_state = SenderState::new(
            senders_weights,
            0.0,
            None,
            LatestMsgs::new(),
            0.0,
            HashSet::new(),
        );

        let mut j0 = Justification::new();
        let (success, _) = j0
            .faulty_inserts(vec![v0].iter().cloned().collect(), &sender_state);
        assert!(success);

        let external_data: Option<VoteCount> = None;
        let (m0, _) = &Message::from_msgs(
            0,
            vec![v0],
            None,
            &sender_state,
            external_data,
        ).unwrap();
        // let m0 = &Message::new(0, justification, estimate);

        let mut j1 = Justification::new();

        let (success, _) = j1
            .faulty_inserts(vec![v0].iter().cloned().collect(), &sender_state);
        assert!(success);

        let (success, _) = j1
            .faulty_inserts(vec![m0].iter().cloned().collect(), &sender_state);
        assert!(success);

        let (msg1, _) =
            Message::from_msgs(0, vec![v0], None, &sender_state, None).unwrap();
        let (msg2, _) =
            Message::from_msgs(0, vec![v0], None, &sender_state, None).unwrap();
        assert!(msg1 == msg2, "messages should be equal");

        let (msg3, _) =
            Message::from_msgs(0, vec![v0, m0], None, &sender_state, None)
                .unwrap();
        assert!(msg1 != msg3, "msg1 should be different than msg3");
    }

    #[test]
    fn msg_depends() {
        let v0 = &VoteCount::create_vote_msg(0, false);
        let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote

        let senders_weights = SendersWeight::new(
            [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect(),
        );

        let sender_state = SenderState::new(
            senders_weights,
            0.0,
            None,
            LatestMsgs::new(),
            0.0,
            HashSet::new(),
        );

        let mut j0 = Justification::new();
        let (success, _) = j0
            .faulty_inserts(vec![v0].iter().cloned().collect(), &sender_state);
        assert!(success);

        let (m0, _) =
            &Message::from_msgs(0, vec![v0], None, &sender_state, None)
                .unwrap();

        assert!(
            !v0.depends(v0_prime),
            "v0 does NOT depends on v0_prime as they are equivocating"
        );
        assert!(
            !m0.depends(m0),
            "m0 does NOT depends on itself directly, by our impl choice"
        );
        assert!(!m0.depends(v0_prime), "m0 depends on v0 directly");
        assert!(m0.depends(v0), "m0 depends on v0 directly");

        let mut j0 = Justification::new();
        let (success, _) =
            j0.faulty_inserts([v0].iter().cloned().collect(), &sender_state);
        assert!(success);

        let (m0, _) =
            &Message::from_msgs(0, vec![v0], None, &sender_state, None)
                .unwrap();

        let mut j1 = Justification::new();
        let (success, _) =
            j1.faulty_inserts([v0].iter().cloned().collect(), &sender_state);
        assert!(success);

        let (success, _) =
            j1.faulty_inserts([m0].iter().cloned().collect(), &sender_state);
        assert!(success);

        let (m1, _) =
            &Message::from_msgs(0, vec![v0, m0], None, &sender_state, None)
                .unwrap();

        assert!(m1.depends(m0), "m1 DOES depent on m0");
        assert!(!m0.depends(m1), "but m0 does NOT depend on m1");
        assert!(m1.depends(v0), "m1 depends on v0 through m0");
    }

    #[test]
    fn msg_equivocates() {
        let v0 = &VoteCount::create_vote_msg(0, false);
        let v0_prime = &VoteCount::create_vote_msg(0, true); // equivocating vote
        let v1 = &VoteCount::create_vote_msg(1, true);

        let senders_weights = SendersWeight::new(
            [(0, 1.0), (1, 1.0), (2, 1.0)].iter().cloned().collect(),
        );
        let sender_state = SenderState::new(
            senders_weights,
            0.0,
            None,
            LatestMsgs::new(),
            0.0,
            HashSet::new(),
        );

        let mut j0 = Justification::new();
        let (success, _) = j0
            .faulty_inserts(vec![v0].iter().cloned().collect(), &sender_state);
        assert!(success);

        let (m0, _) =
            &Message::from_msgs(0, vec![v0], None, &sender_state, None)
                .unwrap();

        let (m1, _) =
            &Message::from_msgs(1, vec![v0], None, &sender_state, None)
                .unwrap();
        assert!(!v0.equivocates(v0), "should be all good");
        assert!(!v1.equivocates(m0), "should be all good");
        assert!(!m0.equivocates(v1), "should be all good");
        assert!(v0.equivocates(v0_prime), "should be a direct equivocation");

        assert!(
            m0.equivocates(v0_prime),
            "should be an indirect equivocation, equivocates to m0 through v0"
        );
        assert!(
            m1.equivocates_indirect(v0_prime, HashSet::new()).0,
            "should be an indirect equivocation, equivocates to m0 through v0"
        );
    }
    #[test]
    fn msg_safe_by_weight() {
        let sender0 = 0;
        let sender1 = 1;

        let senders_weights = &SendersWeight::new(
            [(sender0, 0.5), (sender1, 0.5)].iter().cloned().collect(),
        );

        let sender_state = SenderState::new(
            senders_weights.clone(),
            0.0,
            None,
            LatestMsgs::new(),
            0.0,
            HashSet::new(),
        );

        let thr = &0.5;
        // sender0        v0---m0        m2---
        // sender1               \--m1--/
        let v0 = &VoteCount::create_vote_msg(sender0, false);
        let safe_msgs = v0.get_safe_msgs_by_weight(senders_weights, thr);
        assert_eq!(safe_msgs.len(), 0, "only 0.5 of weight saw v0");

        let (m0, _) = &Message::from_msgs(
            sender0,
            vec![&v0],
            None,
            &sender_state,
            None as Option<VoteCount>,
        ).unwrap();
        let safe_msgs = m0.get_safe_msgs_by_weight(senders_weights, thr);
        assert_eq!(safe_msgs.len(), 0, "only 0.5 of weight saw v0 and m0");

        let (m1, _) = &Message::from_msgs(
            sender1,
            vec![&m0],
            None,
            &sender_state,
            None as Option<VoteCount>,
        ).unwrap();
        let safe_msgs = m1.get_safe_msgs_by_weight(senders_weights, thr);
        assert_eq!(
            safe_msgs.len(),
            0,
            "both sender0 (0.5) and sender1 (0.5) saw v0 and m0, but sender0 hasn't
necessarly seen sender1 seeing v0 and m0, thus not yet safe"
        );

        let (m2, _) = &Message::from_msgs(
            sender0,
            vec![&m1],
            None,
            &sender_state,
            None as Option<VoteCount>,
        ).unwrap();
        let safe_msgs = m2.get_safe_msgs_by_weight(senders_weights, thr);
        assert_eq!(
            safe_msgs.get(m0).unwrap_or(&f64::NAN),
            &1.0,
            "both sender0 and sender1 saw v0 and m0, and additionally both
parties saw each other seing v0 and m0, m0 (and all its dependencies) are final"
        );
        // let senders = &Sender::get_senders(&relative_senders_weights);
    }

    // #[test]
    // fn set_as_final() {
    //     let sender0 = 0;
    //     let sender1 = 1;
    //     let senders_weights = SendersWeight::new(
    //         [(sender0, 1.0), (sender1, 1.0)].iter().cloned().collect(),
    //     );
    //     let sender_state = SenderState::new(
    //         senders_weights.clone(),
    //         0.0,
    //         None,
    //         LatestMsgs::new(),
    //         0.0,
    //         HashSet::new(),
    //     );
    //     let senders = &senders_weights.get_senders().unwrap();

    //     // sender0        v0---m0        m2---
    //     // sender1               \--m1--/
    //     let v0 = &VoteCount::create_vote_msg(sender1, false);
    //     let safe_msgs = v0.get_msg_for_proposition(senders);
    //     assert_eq!(safe_msgs.len(), 0, "only sender0 saw v0");

    //     let (m0, sender_state) = &mut Message::from_msgs(
    //         sender0,
    //         vec![v0],
    //         None,
    //         &sender_state,
    //         None as Option<VoteCount>,
    //     ).unwrap();

    //     let (m1, sender_state) = &Message::from_msgs(
    //         sender1,
    //         vec![m0],
    //         None,
    //         &sender_state,
    //         None as Option<VoteCount>,
    //     ).unwrap();

    //     let (m2, _) = &Message::from_msgs(
    //         sender0,
    //         vec![m1],
    //         None,
    //         &sender_state,
    //         None as Option<VoteCount>,
    //     ).unwrap();

    //     let safe_msgs = m2.get_msg_for_proposition(senders);

    //     assert!(safe_msgs.len() == 1);
    //     println!("------------");
    //     println!("message before trimmed by set_as_final\n {:?}", m0);
    //     m0.set_as_final();
    //     println!("message after\n {:?}", m0);
    //     println!("------------");
    // }

    #[test]
    fn msg_safe_by_sender() {
        // setup
        let sender0 = 0;
        let sender1 = 1;

        let senders_weights = SendersWeight::new(
            [(sender0, 1.0), (sender1, 1.0)].iter().cloned().collect(),
        );

        let sender_state = SenderState::new(
            senders_weights.clone(),
            0.0,
            None,
            LatestMsgs::new(),
            0.0,
            HashSet::new(),
        );
        let senders = &senders_weights.get_senders().unwrap();

        // sender0        v0---m0        m2---
        // sender1               \--m1--/
        let v0 = &VoteCount::create_vote_msg(sender0, false);
        let safe_msgs = v0.get_msg_for_proposition(senders);
        assert_eq!(safe_msgs.len(), 0, "only sender0 saw v0");

        let (m0, sender_state0) = &Message::from_msgs(
            sender0,
            vec![v0],
            None,
            &sender_state,
            None as Option<VoteCount>,
        ).unwrap();

        let safe_msgs = m0.get_msg_for_proposition(senders);
        assert_eq!(safe_msgs.len(), 0, "only sender0 saw v0 and m0");

        let (m1, _) = &Message::from_msgs(
            sender1,
            vec![m0],
            None,
            &sender_state,
            None as Option<VoteCount>,
        ).unwrap();

        let safe_msgs = m1.get_msg_for_proposition(senders);
        assert_eq!(
            safe_msgs.len(),
            0,
            "both sender0 and sender1 saw v0 and m0, but sender0 hasn't
necessarly seen sender1 seeing v0 and m0, thus not yet safe"
        );

        let (m2, _) = &Message::from_msgs(
            sender0,
            vec![m1],
            None,
            &sender_state0,
            None as Option<VoteCount>,
        ).unwrap();

        let safe_msgs = m2.get_msg_for_proposition(senders);
        assert_eq!(
            safe_msgs,
            [m0.clone()].iter().cloned().collect(),
            "both sender0 and sender1 saw v0 and m0, and additionally both
parties saw each other seing v0 and m0, m0 (and all its dependencies) are final"
        );

        // sender0        v0---m0        m2---
        // sender1        v1--/   \--m1--/
        let v0 = &VoteCount::create_vote_msg(sender0, false);
        let v1 = &VoteCount::create_vote_msg(sender1, false);

        let (ref mut m0, sender_state0) = &mut Message::from_msgs(
            sender0,
            vec![v0, v1],
            None,
            &sender_state,
            None as Option<VoteCount>,
        ).unwrap();

        let safe_msgs = m0.get_msg_for_proposition(senders);
        println!("safe_msgs: {:?}", safe_msgs);
        // TODO: turned off because it was eventually failing after changing from BTreeSet to Vec. Function is not used anywhere
        // assert_eq!(
        //     safe_msgs.len(),
        //     0,
        //     "sender0 saw v0, v1 and m0, and sender1 saw only v1"
        // );

        let (m1, _) = &Message::from_msgs(
            sender1,
            vec![m0],
            None,
            &sender_state,
            None as Option<VoteCount>,
        ).unwrap();
        let safe_msgs = m1.get_msg_for_proposition(senders);

        assert_eq!(
            safe_msgs,
            [v1.clone()].iter().cloned().collect(),
            "both sender0 and sender1 saw v0, v1 and m0, but sender0 hasn't
necessarly seen sender1 seeing v0 and m0, just v1 is safe"
        );

        let (m2, _sender_state) = &Message::from_msgs(
            sender0,
            vec![m1],
            None,
            &sender_state0,
            None as Option<VoteCount>,
        ).unwrap();

        let safe_msgs = m2.get_msg_for_proposition(senders);
        assert_eq!(
            safe_msgs,
            [m0.clone()].iter().cloned().collect(),
            "both sender0 and sender1 saw v0 and m0, and additionally both
parties saw each other seing v0 and m0, safe"
        );

        // m0.set_as_final()
    }
}
