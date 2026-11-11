//! pageproof-core: a Verus-verified KV block manager and slab coordinator implementing contract
//! v0.3 (the v0.2.1 single-class manager is the paged-class building block).
#![allow(unused_imports)]
// `verus!` expands ghost-only items/braces that rustc reports as unused or redundant.
#![allow(unused_braces, dead_code)]

pub mod spec;
pub mod e8;
pub mod arith;
pub mod idxset;
pub mod index;
pub mod types;
pub mod model;
pub mod manager;
pub mod ops_release;
pub mod ops_attach;
pub mod ops_extend;
pub mod ops_write;
pub mod ops_slab;
pub mod state;
pub mod cnt;
pub mod coord;
pub mod slabplan;
pub mod coord_attach;
pub mod coord_ops;

use vstd::prelude::*;

verus! {

global size_of usize == 8;

} // verus!
