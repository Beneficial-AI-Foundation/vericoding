// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn ediff1d_precondition(ary: Vec<i8>) -> bool { ary.len() > 0 }
// </vc-helpers>

// <vc-spec>
fn numpy_ediff1d(ary: Vec<i8>) -> (result: Vec<i8>)
    requires ary.len() > 0,
    ensures 
        result.len() == ary.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == ary[i + 1] as int - ary[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed unnecessary `as int` casts for `ary[i as usize + 1]` and `ary[i as usize]` when calculating `diff`. This was causing compilation errors because `ary` elements are already `i8`, eliminating the need to cast them to `int` within the `let diff` assignment. The proof block already correctly handled the `int` casting for verification. */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < ary.len() - 1
        invariant
            0 <= i as int,
            i as int <= (ary.len() - 1) as int,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == ary[j + 1] as int - ary[j] as int,
            ary.len() > 0,
        decreases (ary.len() - 1) - i
    {
        // Prove that the difference fits in i8 and does not overflow/underflow
        proof {
            let diff_val = ary[i as usize + 1] as int - ary[i as usize] as int;
            assert(-128 <= diff_val);
            assert(diff_val <= 127);
        }
        let diff: i8 = (ary[i as usize + 1] - ary[i as usize]) as i8;
        result.push(diff);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}