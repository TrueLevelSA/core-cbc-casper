use std::ops::Add;
use std::hash::{Hash, Hasher};
use std::collections::{HashSet};
// use std::iter::FromIterator;

#[derive(Debug, Eq)]
struct Message<'z> {
    estimate: Option<VoteCounter>,
    sender: Sender,
    justifications: HashSet<&'z Message<'z>>,
}

type Sender = u32;

//// START double vote prevention
// this prevents the same sender from voting twice, but its a bit of a hack. the
// sender id by itself determines whether two messages are the same (because
// they have the same hash, as the hash is computed using only the sender). if
// two msgs are considered the same, only one can be in the set, the one added
// to the set first. should do this more cleanly, although using the same logic
// of sets. i guess would be best to create a Vote type

impl<'z> Hash for Message<'z> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.sender.hash(state);
        // self.estimate.hash(state);
        // self.justifications.hash(state);
    }
}

impl<'z> PartialEq for Message<'z> {
    fn eq(&self, other: &Message<'z>) -> bool {
        self.sender == other.sender
    }
}
//// END double vote prevention

impl<'z> Message<'z> {
    fn endorser(sender: Sender, justifications: HashSet<&'z Message<'z>>) -> Message<'z> {
        Message {
            estimate: Some(estimator(justifications.clone(), sender)),
            sender,
            justifications,
        }
    }
    fn voter(sender: Sender, vote: bool) -> Message<'z> {
        let justifications: HashSet<&'z Message<'z>> = HashSet::new();
        Message {
            estimate: match vote {
                true  => Some(VoteCounter {yes: 1, no: 0, sender: Some(sender)}),
                false => Some(VoteCounter {yes: 0, no: 1, sender: Some(sender)}),
            },
            sender,
            justifications,
        }
    }
}

#[derive(Clone, Debug, Hash, Eq)]
struct VoteCounter {
    yes: u32,
    no: u32,
    sender: Option<Sender>,
}

impl Add for VoteCounter {
    type Output = VoteCounter;
    fn add(self, other: VoteCounter) -> VoteCounter {
        VoteCounter { yes: self.yes + other.yes, no: self.no + other.no, sender: None }
    }
}

impl PartialEq for VoteCounter {
    fn eq(&self, other: &VoteCounter) -> bool {
        self.yes == other.yes && self.no == other.no
    }
}

fn get_votes<'z>(msg: &'z Message, acc: HashSet<&'z Message<'z>>) -> HashSet<&'z Message<'z>> {
    msg.justifications.iter()
        .fold(acc, |mut acc_new, m| {
            match m.justifications.len() {
                0 => { // vote found, vote is a message with 0 justifications
                    acc_new.insert(m);
                    acc_new
                },
                _ => get_votes(m, acc_new),
            }
        })
}

fn estimator (justifications: HashSet<&Message>, sender: Sender) -> VoteCounter {
    let msg = Message { estimate: None, sender, justifications }; // stub msg w/ no estimate
    let votes = get_votes(&msg, HashSet::new());
    votes.iter()
        .fold(VoteCounter{ yes: 0, no: 0, sender: Some(sender) }, |acc, vote| {
            match &vote.estimate {
                Some(estimate) => acc + estimate.clone(),
                None => acc, // skip counting
            }
        })
}

fn main () {
    // original votes
    let v0 = Message::voter(0, false);
    let v4 = Message::voter(0, true); // double vote
    let v1 = Message::voter(1, true);
    let v2 = Message::voter(2, true);
    let v3 = Message::voter(3, true);

    let m0 = Message::endorser(0, [&v0].iter().cloned().collect());
    assert!(m0.estimate == Some(VoteCounter {yes: 0, no: 1, sender: None}), "should have 0 yes, and 1 no vote");

    let m1 = Message::endorser(1, [&v1, &m0, &v4].iter().cloned().collect());
    assert!(m1.estimate == Some(VoteCounter {yes: 1, no: 1, sender: None}), "should have 1 yes, and 1 no vote");

    let m2 = Message::endorser(2, [&v2, &m0, &m1].iter().cloned().collect());
    assert!(m2.estimate == Some(VoteCounter {yes: 2, no: 1, sender: None}), "should have 2 yes, and 1 no vote");

    let m3 = Message::endorser(0, [&m1, &m2].iter().cloned().collect());
    assert!(m3.estimate == Some(VoteCounter {yes: 2, no: 1, sender: None}), "should have 2 yes, and 1 no vote");

    let m4 = Message::endorser(3, [&v3, &m0, &m1, &m2, &m3].iter().cloned().collect());
    assert!(m4.estimate == Some(VoteCounter {yes: 3, no: 1, sender: None}), "should have 3 yes, and 1 no vote");
}
