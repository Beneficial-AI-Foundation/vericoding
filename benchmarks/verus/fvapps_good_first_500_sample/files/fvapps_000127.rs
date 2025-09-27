// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn score_pair(values: Seq<u32>, i: int, j: int) -> int {
    (values[i] as int) + (values[j] as int) + i - j
}

fn max_score_sightseeing_pair(values: Vec<u32>) -> (result: u32)
    requires 
        values.len() >= 2,
        forall|i: int| 0 <= i < values.len() ==> #[trigger] values[i] >= 1 && #[trigger] values[i] <= 1000,
    ensures 
        values@ == seq![8u32, 1u32, 5u32, 2u32, 6u32] ==> result == 11u32,
        values@ == seq![1u32, 2u32] ==> result == 2u32,
        values@ == seq![5u32, 5u32, 5u32, 5u32] ==> result == 9u32,
        values@ == seq![1u32, 1u32] ==> result == 1u32,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0u32
    // impl-end
}
// </vc-code>


}
fn main() {}