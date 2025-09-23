// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn two_sum(nums: &Vec<i32>, target: i32) -> (result: Vec<usize>)
    requires 
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= j < i < nums.len() && nums[i] + nums[j] == target,
        forall|i1: int, j1: int, i2: int, j2: int| 
            (0 <= j1 < i1 < nums.len() && nums[i1] + nums[j1] == target &&
             0 <= j2 < i2 < nums.len() && nums[i2] + nums[j2] == target) ==> 
            (i1 == i2 && j1 == j2),
    ensures
        result.len() == 2,
        result[0] < nums.len(),
        result[1] < nums.len(),
        result[0] < result[1],
        nums[result[0] as int] + nums[result[1] as int] == target,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}