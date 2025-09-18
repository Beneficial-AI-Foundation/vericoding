// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn two_sum(nums: &Vec<i32>, target: i32) -> (result: (usize, usize))
    requires
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        result.0 < result.1,
        result.0 < nums.len(),
        result.1 < nums.len(),
        nums[result.0 as int] + nums[result.1 as int] == target,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use usize indices directly for Vec indexing, cast to i64 for addition to prevent overflow during verification */
    for i in 0..nums.len() {
        for j in (i + 1)..nums.len() {
            if (nums[i] as i64 + nums[j] as i64) == (target as i64) {
                return (i, j);
            }
        }
    }
    assert(false); // Spec guarantees existence, so unreachable
    (0, 1)
}
// </vc-code>

}
fn main() {}