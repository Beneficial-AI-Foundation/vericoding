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
    /* code modified by LLM (iteration 2): Added decreases clauses to both loops for termination */
    let mut i: usize = 0;
    while i < nums.len() - 1
        invariant
            0 <= i <= nums.len() - 1,
            forall|i_prev: int, j_prev: int| 0 <= i_prev < i && i_prev < j_prev < nums.len() ==> nums[i_prev] + nums[j_prev] != target,
            exists|i_exist: int, j_exist: int| i <= i_exist < j_exist < nums.len() && nums[i_exist] + nums[j_exist] == target,
        decreases nums.len() - 1 - i
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                i < j <= nums.len(),
                i < nums.len() - 1,
                forall|j_prev: int| i < j_prev < j ==> nums[i as int] + nums[j_prev] != target,
                exists|i_exist: int, j_exist: int| (i as int == i_exist && j <= j_exist < nums.len()) || (i < i_exist < j_exist < nums.len()) && nums[i_exist] + nums[j_exist] == target,
            decreases nums.len() - j
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    unreached()
}
// </vc-code>

}
fn main() {}