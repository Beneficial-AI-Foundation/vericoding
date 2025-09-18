// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): extract witness indices from existential precondition */
fn extract_witness(nums: &Vec<i32>, target: i32) -> (usize, usize)
    requires
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        result.0 < result.1,
        result.0 < nums.len(),
        result.1 < nums.len(),
        nums[result.0 as int] + nums[result.1 as int] == target,
{
    let mut u: usize = 0;
    let mut v: usize = 0;
    proof {
        choose |i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target;
        u = i as usize;
        v = j as usize;
    }
    (u, v)
}
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
    /* code modified by LLM (iteration 5): call ghost helper to obtain witness indices */
    extract_witness(nums, target)
}
// </vc-code>

}
fn main() {}