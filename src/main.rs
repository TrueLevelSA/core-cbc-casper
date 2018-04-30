use std::ops::Add;
use std::hash::{Hash, Hasher};
use std::collections::{HashSet};

#[derive(Debug, Eq, PartialEq)]
struct Message<'z> {
    estimate: Option<VoteCounter>,
    sender: Sender,
    justifications: HashSet<&'z Message<'z>>,
}

type Sender = u32;

impl<'z> Hash for Message<'z> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.estimate.hash(state);
        self.sender.hash(state);
        // self.justifications.hash(state);
    }
}

impl<'z> Message<'z> {
    fn relayer(sender: Sender, justifications: HashSet<&'z Message<'z>>) -> Message<'z> {
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
                true  => Some(VoteCounter {yes: 1, no: 0, sender}),
                false => Some(VoteCounter {yes: 0, no: 1, sender}),
            },
            sender,
            justifications,
        }
    }
}

#[derive(Clone, Debug, Hash)]
struct VoteCounter {
    yes: u32,
    no: u32,
    sender: Sender,
}

impl Add for VoteCounter {
    type Output = VoteCounter;
    fn add(self, other: VoteCounter) -> VoteCounter {
        VoteCounter { yes: self.yes + other.yes, no: self.no + other.no, ..self }
    }
}

impl PartialEq for VoteCounter {
    fn eq(&self, other: &VoteCounter) -> bool {
        self.sender == other.sender
            // && self.yes == other.yes
            // && self.no == other.no
    }
}

impl Eq for VoteCounter { }

fn get_votes<'z>(msg: &'z Message, acc: HashSet<&'z Message<'z>>) -> HashSet<&'z Message<'z>> {
    msg.justifications.iter()
        .fold(acc, |mut acc_new, m| {
            match m.justifications.len() {
                0 => { // vote found, vote is a message with 0 justifications
                    acc_new.insert(m); // mutates acc_new
                    acc_new // return it
                },
                _ => get_votes(m, acc_new),
            }
        })
}

fn estimator (justifications: HashSet<&Message>, sender: Sender) -> VoteCounter {
    let msg = Message {estimate: None, sender, justifications }; // stub msg w/ no estimate
    let votes = get_votes(&msg, HashSet::new());
    votes.iter()
        .fold(VoteCounter{ yes: 0, no: 0, sender }, |acc, vote| {
            match &vote.estimate {
                Some(estimate) => acc + estimate.clone(),
                None => acc, // skip counting
            }
        })
}

fn main () {
    // original votes
    let v0 = Message::voter(0, false);
    // let v4 = Message::voter(0, true);
    let v1 = Message::voter(1, true);
    let v2 = Message::voter(2, true);
    let v3 = Message::voter(3, true);

    println!("\nMessage: m0");
    let m0 = Message::relayer(0, [&v0].iter().cloned().collect());
    println!("estimate: {:?}", m0.estimate);

    println!("\nMessage: m1");
    let m1 = Message::relayer(1, [&v1, &m0].iter().cloned().collect());
    println!("estimate: {:?}", m1.estimate);

    println!("\nMessage: m2");
    let m2 = Message::relayer(2, [&v2, &m0, &m1].iter().cloned().collect());
    println!("estimate: {:?}", m2.estimate);

    println!("\nMessage: m3");
    let m3 = Message::relayer(0, [&m1, &m2].iter().cloned().collect());
    println!("estimate: {:?}", m3.estimate);

    println!("\nMessage: m4");
    let m4 = Message::relayer(3, [&v3, &m0, &m1, &m2, &m3].iter().cloned().collect());
    println!("estimate: {:?}", m4.estimate);
    // let h4 = calc_hash(&m4);
    // println!("{:?}", h4);
    // println!("{:?}", estimator(&vec![&m2, &m4]));
}
