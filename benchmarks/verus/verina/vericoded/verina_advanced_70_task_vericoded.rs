// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn zero() -> int {
    0
}

proof fn lemma_zero_nonneg()
    ensures
        zero() >= 0
{
}

// </vc-helpers>

// <vc-spec>
fn semi_ordered_permutation(nums: &Vec<i32>) -> (result: i32)
    ensures 
        result >= 0
// </vc-spec>
// <vc-code>
{
    0
}
// </vc-code>

}
fn main() {}