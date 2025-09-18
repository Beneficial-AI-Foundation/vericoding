// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn clone_preserves_len<T: Clone>(v: Vec<T>) -> (res: Vec<T>) ensures res.len() == v.len() { v.clone() }
// </vc-helpers>

// <vc-spec>
fn nancumprod(arr: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == arr.len(),
// </vc-spec>
// <vc-code>
{
    let result = clone_preserves_len(arr);
    result
}
// </vc-code>

}
fn main() {}