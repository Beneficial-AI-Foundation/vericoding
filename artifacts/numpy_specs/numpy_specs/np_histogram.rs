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
    // Empty implementation - just create a vector of the right size
    let mut hist = Vec::new();
    let mut j: usize = 0;
    while j < bins.len() - 1
        invariant 
            hist.len() == j,
            j <= bins.len() - 1,
        decreases bins.len() - 1 - j
    {
        hist.push(0);
        j += 1;
    }
    hist
}

// SPEC
fn histogram_helper(data: &[i32], bins: &[i32], hist: &mut Vec<i32>, index: usize)
    requires
        bins.len() >= 2,
        forall|i: int| 1 <= i < bins.len() ==> bins[i] > bins[#[trigger](i-1)],
{
    // Empty implementation
}

fn main() {}

}