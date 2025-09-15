// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed. */
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
/* code modified by LLM (iteration 5): Fixed a compilation error regarding comma in invariant. */
{
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i as int && i as int <= nums.len() as int,
            forall|k: int, l: int|
                0 <= k < l < i as int ==> nums[k] + nums[l] != target,
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                i as int < j as int && j as int <= nums.len() as int,
                forall|k: int, l: int|
                    (0 <= k < l < i as int || (k == i as int && i as int < l && l < j as int)) ==> nums[k] + nums[l] != target,
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    proof {
        let (req_i, req_j): (int, int) = choose |k: int, l: int| 0 <= k < l < nums.len() as int && nums[k] + nums[l] == target;
        assert(exists|m: int, n: int| 0<=m < n < nums.len() as int && nums[m] + nums[n] == target);
    }
    (0, 1)
}
// </vc-code>

}
fn main() {}