use traits::Sender;

use example::binary::BoolWrapper;
use example::integer::IntegerWrapper;
use example::vote_count::{VoteCount};
use example::blockchain::{Block, ProtoBlock};

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
