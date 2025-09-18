// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax error by adding 'as int' for nums.len() */
proof fn lemma_exists_pair(nums: &Vec<i32>, target: i32, i: usize)
    requires
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        i < nums.len(),
        forall|k: int, l: int| 0 <= k < l < nums.len() && k < i as int ==> nums[k] + nums[l] != target,
    ensures
        exists|j: int| i as int < j < nums.len() as int && nums[i as int] + nums[j as int] == target,
{
    assert(exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target);
}
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
/* code modified by LLM (iteration 5): No changes needed - code is correct */
{
    let mut i: usize = 0;
    while i < nums.len() - 1
        invariant
            i < nums.len(),
            nums.len() > 1,
            exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
            forall|k: int, l: int| 0 <= k < l < nums.len() && k < i as int ==> nums[k] + nums[l] != target,
    {
        lemma_exists_pair(nums, target, i);
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                i < j,
                j <= nums.len(),
                i < nums.len() - 1,
                nums.len() > 1,
                exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
                forall|k: int| i as int < k < j as int ==> nums[i as int] + nums[k] != target,
                forall|k: int, l: int| 0 <= k < l < nums.len() && k < i as int ==> nums[k] + nums[l] != target,
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