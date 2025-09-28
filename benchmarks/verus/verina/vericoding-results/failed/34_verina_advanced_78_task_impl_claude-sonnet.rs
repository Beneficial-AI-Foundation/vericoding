// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma to handle arithmetic overflow bounds */
proof fn lemma_no_overflow(nums: &Vec<i32>, i: usize, j: usize)
    requires
        i < nums.len(),
        j < nums.len(),
    ensures
        nums[i as int] + nums[j as int] == (nums[i] + nums[j]) as int,
{
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
    /* code modified by LLM (iteration 5): fixed invariant and overflow issues */
    for i in 0..nums.len()
        invariant
            forall|k: int, l: int| 0 <= k < l < i ==> nums[k] + nums[l] != target,
    {
        for j in (i + 1)..nums.len()
            invariant
                i < nums.len(),
                forall|k: int, l: int| 0 <= k < l < i ==> nums[k] + nums[l] != target,
                forall|l: int| i < l < j ==> nums[i as int] + nums[l] != target,
        {
            proof {
                lemma_no_overflow(nums, i, j);
            }
            if nums[i] + nums[j] == target {
                proof {
                    assert(nums[i as int] + nums[j as int] == target);
                }
                return (i, j);
            }
        }
    }
    unreached()
}
// </vc-code>

}
fn main() {}