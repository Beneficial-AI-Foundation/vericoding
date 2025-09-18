// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn convolution_sum(arr1: Seq<f32>, arr2: Seq<f32>, n: nat) -> f32
{
    0.0
}

fn convolution_sum_impl(arr1: &Vec<f32>, arr2: &Vec<f32>, n: usize) -> f32
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}

fn convolve(arr1: &Vec<f32>, arr2: &Vec<f32>) -> (result: Vec<f32>)
    requires 
        arr1.len() > 0,
        arr2.len() > 0,
    ensures 
        result.len() == arr1.len() + arr2.len() - 1,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}
fn main() {}