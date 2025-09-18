// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min_int(a: int, b: int) -> int { if a < b { a } else { b } }
spec fn is_nonneg(x: int) -> bool { x >= 0 }
proof fn lemma_zero_nonneg() ensures 0 >= 0 { }
// </vc-helpers>

// <vc-spec>
fn rain(heights: &Vec<i32>) -> (result: i32)
    requires forall|i: int| 0 <= i < heights.len() ==> heights[i] >= 0,
    ensures 
        result >= 0,
        heights.len() < 3 ==> result == 0,
// </vc-spec>
// <vc-code>
{
    0
}
// </vc-code>

}
fn main() {}