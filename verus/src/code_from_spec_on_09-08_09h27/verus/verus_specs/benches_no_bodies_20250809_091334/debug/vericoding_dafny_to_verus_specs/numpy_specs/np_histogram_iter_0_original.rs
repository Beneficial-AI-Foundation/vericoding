use vstd::prelude::*;

verus! {

// SPEC
fn histogram(data: &[i32], bins: &[i32]) -> (hist: Vec<i32>)
    requires 
        bins.len() >= 2,
        forall|i: int| 1 <= i < bins.len() ==> bins[i] > bins[#[trigger](i-1)],
    ensures
        hist.len() == bins.len() - 1,
        data.len() >= 0,
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

// SPEC
fn histogram_helper(data: &[i32], bins: &[i32], hist: &mut Vec<i32>, index: usize)
    requires
        bins.len() >= 2,
        forall|i: int| 1 <= i < bins.len() ==> bins[i] > bins[#[trigger](i-1)],
{
    // TODO: Remove this comment and implement the function body
}

fn main() {}

}