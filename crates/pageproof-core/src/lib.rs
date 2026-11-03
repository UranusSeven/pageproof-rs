//! pageproof-core: a Verus-verified KV block manager implementing contract v0.2.1.
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

use vstd::prelude::*;

verus! {

global size_of usize == 8;

} // verus!
