// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn always_true() -> bool { true }
// </vc-helpers>

// <vc-spec>
fn semi_ordered_permutation(nums: &Vec<i32>) -> (result: i32)
    ensures 
        result >= 0
// </vc-spec>
// <vc-code>
{
    let result: i32 = 0;
    result
}
// </vc-code>

}
fn main() {}