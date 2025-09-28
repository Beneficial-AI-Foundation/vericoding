// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn nonzero_helper(arr: Seq<f32>) -> nat 
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else {
        let rest_count = nonzero_helper(arr.skip(1));
        if arr[0] == 0.0f32 {
            rest_count
        } else {
            rest_count + 1
        }
    }
}

fn nonzero(arr: Vec<f32>) -> (result: usize)
    ensures 
        result <= arr.len(),
        result == nonzero_helper(arr@),
        arr.len() > 0 && arr[0] == 0.0f32 ==> 
            nonzero_helper(arr@.skip(1)) == if result > 0 { result - 1 } else { 0 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix loop invariant and arithmetic overflow */
    let mut count = 0;
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            count == nonzero_helper(arr@.subrange(0, i as int)),
            count <= i,
        decreases arr.len() - i
    {
        if arr[i] != 0.0f32 {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>


}
fn main() {}