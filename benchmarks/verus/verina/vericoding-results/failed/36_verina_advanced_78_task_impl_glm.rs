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
    /* code modified by LLM (iteration 4): fixed invariant syntax by splitting chained comparisons */
    let n = nums.len();
    let mut i = 0;
    while i < n - 1
        invariant 0 <= i as int, i as int < n as int
    {
        let mut j = i + 1;
        while j < n
            invariant (i+1) as int <= j as int, j as int <= n as int
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        assert(false);
    }
    (0, 0)
}
// </vc-code>

}
fn main() {}