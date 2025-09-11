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
        result.1 < nums.len(),
        nums[result.0 as int] + nums[result.1 as int] == target,
        forall|i: int, j: int| 0 <= i < j < nums.len() && i < result.0 as int ==> nums[i] + nums[j] != target,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}