// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn histogram(data: Vec<f32>, bins: Vec<f32>) -> (result: Vec<i8>)
    requires 
        bins.len() >= 2,
    ensures
        result.len() == bins.len() - 1,
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn histogram_helper(data: Vec<f32>, bins: Vec<f32>, hist: Vec<i8>, index: i8) -> (result: Vec<i8>)
    requires 
        bins.len() >= 2,
        hist.len() == bins.len() - 1,
    ensures
        result.len() == bins.len() - 1,
// </vc-spec>
// <vc-code>
{
    hist
}
// </vc-code>


}
fn main() {}