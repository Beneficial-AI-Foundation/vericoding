// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary helper section, as `subsequence` is now correctly identified as `Seq::subsequence` */
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
/* code modified by LLM (iteration 5): Corrected `subsequence` call to `Seq::subsequence` and simplified spec invariant. */
{
    let mut count: usize = 0;
    let mut i: usize = 0;

    while i < arr.len()
        invariant 
            count <= i,
            count == nonzero_helper(arr@.subsequence(0, i as nat)),
            i <= arr.len()
        decreases arr.len() - i
    {
        if arr@[i] != 0.0f32 {
            count = count + 1;
        };
        i = i + 1;
    }
    
    proof {
        assert(count == nonzero_helper(arr@.subsequence(0, arr.len() as nat)));
    }

    count
}
// </vc-code>


}
fn main() {}