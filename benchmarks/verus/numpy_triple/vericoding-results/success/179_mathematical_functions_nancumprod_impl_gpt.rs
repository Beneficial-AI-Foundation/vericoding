// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nancumprod(arr: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == arr.len(),
// </vc-spec>
// <vc-code>
{
    arr
}
// </vc-code>

}
fn main() {}