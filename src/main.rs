use std::collections::{BTreeSet, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Add;
// use std::cmp::Ordering;
// use std::iter::FromIterator;

type Sender = u32;

#[derive(Eq, Ord, PartialOrd)]
struct Message<'z> {
    estimate: Option<VoteCount>,
    sender: Sender,
    justifications: Justifications<'z>,
    sequence: Option<u32>, // TODO shouldn't be necessary, but handy
}

impl<'z> Message<'z> {
    fn endorser(sender: Sender, justifications: Justifications<'z>, sequence: u32) -> Message<'z> {
        Message {
            estimate: Some(VoteCount::count_votes(justifications.clone(), sender)),
            sender,
            justifications,
            sequence: Some(sequence),
        }
    }
    fn voter(sender: Sender, vote: bool, sequence: u32) -> Message<'z> {
        let justifications: Justifications = Justifications::new();
        Message {
            estimate: match vote {
                true => Some(VoteCount { yes: 1, no: 0 }),
                false => Some(VoteCount { yes: 0, no: 1 }),
            },
            sender,
            justifications,
            sequence: Some(sequence),
        }
    }
    fn depends(m1: &Self, m2: &Self) -> bool {
        m1.justifications.latest_msgs.iter().fold(
            m1.justifications.latest_msgs.contains(m2),
            // the trick on the following recursion is the following: it
            // short-circuits while descending on the thread. when dealing with
            // honest validators, this would return true very fast. all the new
            // derived branches of the justification can be evaluated in
            // parallel.
            |acc, m1_prime| acc || Self::depends(m1_prime, m2),
        )
    }
    fn equivocates(m1: &Self, m2: &Self) -> bool {
        // the estimate bit below is necessary due to the definition of equality
        // of messages (the estimate is not a function of the equality). see
        // tests for equality of messages.
        let equal_msgs = m1 == m2 && m1.estimate == m2.estimate;
        !equal_msgs
            && m1.sender == m2.sender
            // && m1.sequence == m2.sequence // this shouldnt be necessary
            && !Self::depends(m1, m2)
            && !Self::depends(m2, m1)
    }
}

//// START double vote prevention
// this prevents the same sender from voting twice, but its a bit of a hack. the
// sender id by itself determines whether two messages are the same (because
// they have the same hash, as the hash is computed using only the sender). if
// two msgs are considered the same, only one can be in the set, the one added
// to the set first. additionally this enforces that at any justification there
// can only be one message from each sender. should do this more cleanly,
// although using the same logic of sets. i guess would be best to create a Vote
// type

// what happens if in the justification of one of the justifications theres a
// message that is newer than the one referred to in the current justification?

// what happens if a sender does not reference his latest message

impl<'z> Hash for Message<'z> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.sender.hash(state);
        // self.sequence.hash(state);
        self.justifications.hash(state);
        // self.estimate.hash(state); // the hash of the msg does NOT depend on the estimate
    }
}

impl<'z> PartialEq for Message<'z> {
    fn eq(&self, other: &Message<'z>) -> bool {
        self.sender == other.sender
            // && self.sequence == other.sequence
            && self.justifications == other.justifications
        // && self.estimate == other.estimate
    }
}
//// END double vote prevention

impl<'z> fmt::Debug for Message<'z> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Message {{ sender: {}, sequence: {} }} -> {:?}",
            self.sender,
            self.sequence.unwrap_or(0),
            self.justifications
        )
    }
}

#[derive(Eq, PartialEq, Hash, PartialOrd, Ord, Clone)]
// make sure only latest messages can get in the set
struct Justifications<'z> {
    latest_msgs: BTreeSet<&'z Message<'z>>,
    // prev_msg: Option<&'z Message<'z>>,
}

// TODO: BTreeSet is ordered, but all nodes should be able to compute the same
// ordered set based on the content of the message and not memory addresses

// impl Hash for Justifications { }

impl<'z> Justifications<'z> {
    fn new() -> Self {
        Justifications {
            latest_msgs: BTreeSet::new(),
        }
    }

    fn insert(&mut self, msg: &'z Message<'z>) -> bool {
        match self
            .latest_msgs
            .iter()
            .all(|m| !Message::equivocates(m, msg))
        {
            true => self.latest_msgs.insert(msg),
            false => false,
        }
    }
}

impl<'z> fmt::Debug for Justifications<'z> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.latest_msgs)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialOrd)]
struct VoteCount {
    yes: u32,
    no: u32,
}

// the value (z) that, when added to other value (x) of same tyoe, returns the
// other value (x): $x + z = x$
trait Zero<T> {
    const ZERO: T;
}

impl Zero<VoteCount> for VoteCount {
    const ZERO: Self = Self { yes: 0, no: 0 };
}

impl Add for VoteCount {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        VoteCount {
            yes: self.yes + other.yes,
            no: self.no + other.no,
        }
    }
}

impl PartialEq for VoteCount {
    fn eq(&self, other: &VoteCount) -> bool {
        self.yes == other.yes && self.no == other.no
    }
}

impl VoteCount {
    fn get_votes<'z>(msg: &'z Message, acc: HashSet<&'z Message>) -> HashSet<&'z Message<'z>> {
        msg.justifications
            .latest_msgs
            .iter()
            .fold(acc, |mut acc_new, m| {
                match m.justifications.latest_msgs.len() {
                    0 => {
                        // vote found, vote is a message with 0 justifications
                        acc_new.insert(m); // mutates acc_new
                        acc_new // returns the mutated acc_new
                    }
                    _ => Self::get_votes(m, acc_new),
                }
            })
    }
    // makes sure nobody adds more than one vote to their unjustified
    // votecounter. if they did, their vote is invalid and will be ignored
    fn  valid_vote(vote: &Option<VoteCount>) -> bool {
        // these two are the only allowed votes (unjustified msgs)
        vote == &Some(VoteCount { yes: 1, no: 0 })
            || vote == &Some(VoteCount { yes: 0, no: 1 })
    }
    fn count_votes(justifications: Justifications, sender: Sender) -> VoteCount {
        // stub msg w/ no estimate
        let msg = Message {
            estimate: None,
            sender,
            justifications,
            sequence: None,
        };
        let votes = Self::get_votes(&msg, HashSet::new());
        votes.iter()
            .filter(|v| {
                // the estimate here is actually the original votes of each of
                // the voters / validators
                Self::valid_vote(&v.estimate)
            })
            .fold(VoteCount::ZERO, |acc, vote| {
                match &vote.estimate {
                    Some(estimate) => acc + estimate.clone(),
                    None => acc, // skip counting
                }
            })
    }
}

// // show that each vote was seen by all validators
// fn votes_seen<'z>(msg: &'z Message<'z>, mut senders: &'z Vec<Sender>, acc: HashSet<(&'z Message<'z>, &'z Vec<Sender>)>) -> HashSet<(&'z Message<'z>, &'z Vec<Sender>)> {
//     msg.justifications.iter()
//         .fold(acc, |mut acc_new, m| {
//             match m.justifications.len() {
//                 0 => { // vote found, vote is a message with 0 justifications
//                     acc_new.insert((m, &senders)); // mutates acc_new
//                     acc_new // returns the mutated acc_new
//                 },
//                 _ => {
//                     senders.push(m.sender);
//                     votes_seen(m, &senders.clone(), acc_new)
//                 },
//             }
//         })
// }

fn main() {
    let v0 = Message::voter(0, false, 0);
    let v0_prime = Message::voter(0, true, 0); // equivocating vote

    // v0 and v0_prime are equivocating messages (first child of a fork). To
    // enforce that both of them cannot be included in the same set (in a
    // hashset) both v0 and v0_prime should hash to the same value, and should
    // be considered equal, and only one of them could live in the set. To
    // achieve that, the vote itself doesn't count, just sender and
    // justification contributes to the hash (here justification is empty).
    // TODO: What about when a fork happens and the justifications are different
    // but at the same height, i should handle that.
    assert!(v0 == v0_prime, "v0 and v0_prime should be equal");
    assert!(
        Message::equivocates(&v0, &v0_prime),
        "$v0$  and $v0_prime$ are direct equivocations"
    );

    let v1 = Message::voter(1, true, 0);
    assert!(v0 != v1);

    // let v2 = Message::voter(2, true, 0);
    // let v3 = Message::voter(3, true, 0);

    let mut j0 = Justifications::new();
    assert!(j0.insert(&v0));
    let m0 = Message::endorser(0, j0, 1);
    assert_eq!(
        m0.estimate,
        Some(VoteCount { yes: 0, no: 1 }),
        "should have 0 yes, and 1 no vote, found {:?}",
        m0.estimate
    );

    assert!(!Message::equivocates(&v0, &v0), "should be all good");
    assert!(!Message::equivocates(&v1, &m0), "should be all good");
    assert!(!Message::equivocates(&m0, &v1), "should be all good");
    assert!(Message::equivocates(&v0, &v0_prime), "should be a direct equivocation");
    assert!(Message::equivocates(&m0, &v0_prime), "should be an indirect equivocation, equivocates to m0 through v0");

    let mut j1 = Justifications::new();
    assert!(j1.insert(&v1));
    assert!(j1.insert(&m0));

    assert!(
        !j1.insert(&v0_prime),
        "$v0_prime$ should conflict with $v0$ through $m0$"
    );

    let m1 = Message::endorser(1, j1, 1);
    assert_eq!(
        m1.estimate,
        Some(VoteCount { yes: 1, no: 1 }),
        "should have 1 yes, and 1 no vote, found {:?}",
        m1.estimate
    );
    assert!(Message::depends(&m1, &v0), "m1 depends on v0 through m0");
    assert!(Message::depends(&m0, &v0), "m0 depends on v0 directly");

    // println!("m1: {:?}", m1);
    // let mut j2 = Justifications::new(None); assert!(j2.insert(&v0)); assert!(j2.insert(&v0_prime));
    // let m2 = Message::endorser(2, j2, 0);
    // assert_eq!(Justifications::new([&v1, &m0, &v0].iter().cloned().collect(), Some(&m0)), Justifications::new([&v1, &m0, &v0_prime].iter().cloned().collect(), Some(&m0)));

    // assert!(!m1.depends(&v0_prime), "m1 doesnt depends on v0_prime");

    // println!("m0: {:?}", m0.justifications);
    // println!("m1: {:?}", m1.justifications);

    // let m2 = Message::endorser(0, Justifications{latest_msgs: [&m1].iter().cloned().collect()}, 1);
    // let m3 = Message::endorser(0, Justifications{latest_msgs: [&v1].iter().cloned().collect()}, 2);
    // println!("m2: {:?}", m2.justifications);
    // println!("m3: {:?}", m3.justifications);

    // println!("d: {:?}", m0.justifications.set.is_disjoint(&m1.justifications.set));

    // let m1p = Message::endorser(1, [&v1, &v0_prime, &m0].iter().cloned().collect());
    // assert!(m1p.estimate == Some(VoteCount {yes: 2, no: 0, sender: None}), "should have 2 yes, and 0 no vote, found {:?}", m1p.estimate);

    // let m2 = Message::endorser(2, [&v2, &m0, &m1].iter().cloned().collect());
    // assert!(m2.estimate == Some(VoteCount {yes: 2, no: 1, sender: None}), "should have 2 yes, and 1 no vote, found {:?}", m2.estimate);

    // let m3 = Message::endorser(0, [&m0, &m1, &m2].iter().cloned().collect());
    // assert!(m3.estimate == Some(VoteCount {yes: 2, no: 1, sender: None}), "should have 2 yes, and 1 no vote, found {:?}", m3.estimate);

    // let m4 = Message::endorser(3, [&v3, &m0, &m1, &m2, &m3].iter().cloned().collect());
    // assert!(m4.estimate == Some(VoteCount {yes: 3, no: 1, sender: None}), "should have 3 yes, and 1 no vote, found {:?}", m4.estimate);

    // let m5 = Message::endorser(0, [&m0, &m1, &m2, &m3, &m4].iter().cloned().collect());
    // assert!(m5.estimate == Some(VoteCount {yes: 3, no: 1, sender: None}), "should have 3 yes, and 1 no vote, found {:?}", m5.estimate);

    // let m6 = Message::endorser(0, [&m5].iter().cloned().collect());
    // assert!(m6.estimate == Some(VoteCount {yes: 3, no: 1, sender: None}), "should have 3 yes, and 1 no vote, found {:?}", m6.estimate);

    // println!("m0: {:?}", m0.justifications.len());
    // println!("m1: {:?}", m1.justifications.len());
    // println!("m2: {:?}", m2.justifications.len());

    // // let j5: HashSet<_> = [&m1, &m2, &m3].iter().cloned().collect();
    // // let j6: HashSet<_> = [&m4].iter().cloned().collect();
    // // // let m6 = Message::endorser(3, [&m0, &m1, &m2, &m3, &m4, &m5].iter().cloned().collect());
    // // println!("{:?}", j5.len());
    // // println!("{:?}", j6.len());
}
