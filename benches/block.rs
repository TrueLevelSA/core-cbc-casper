#[macro_use]
extern crate criterion;

use casper::Block;
use criterion::{black_box, Criterion};

fn block_new(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "Block::new",
        |b, loops| {
            b.iter(|| {
                let mut block: Option<Block<u8>> = None;
                for _ in 0..(**loops) {
                    block = Some(Block::new(block));
                }
            });
        },
        &[1_000, 10 * 1_000, 100 * 1_000],
    );
}

fn block_from_prevblock_msg(c: &mut Criterion) {
    c.bench_function("Block::from_prevblock_msg", |b| {
        let block: Block<u8> = Block::new(None);
        b.iter(|| {
            Block::from_prevblock_msg(black_box(None), black_box(block.clone()));
        });
    });
}

fn block_is_member(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "Block::is_member",
        |b, loops| {
            let first_block: Block<u8> = Block::new(None);
            let mut block = Block::new(Some(first_block.clone()));
            for _ in 0..(**loops) {
                block = Block::new(Some(block));
            }
            b.iter(|| first_block.is_member(&block));
        },
        &[10, 100, 1_000],
    );
}

criterion_group!(
    benches,
    block_new,
    block_from_prevblock_msg,
    block_is_member
);
criterion_main!(benches);
