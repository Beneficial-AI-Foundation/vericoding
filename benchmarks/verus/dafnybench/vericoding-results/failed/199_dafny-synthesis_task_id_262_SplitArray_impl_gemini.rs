// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split_array(arr: &[i32], l: usize) -> (Vec<i32>, Vec<i32>)
    requires 0 <= l <= arr.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented split using executable slice operations and Vec::from_slice_copy */
    let vec1 = Vec::from_slice_copy(&arr[0..l]);
    let vec2 = Vec::from_slice_copy(&arr[l..]);
    (vec1, vec2)
}
// </vc-code>

}
fn main() {}