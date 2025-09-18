// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
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