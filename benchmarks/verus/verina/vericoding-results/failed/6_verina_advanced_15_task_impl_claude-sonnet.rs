// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed vector indexing to use @ operator */
spec fn has_increasing_triplet_at(nums: &Vec<i32>, i: int, j: int, k: int) -> bool {
    0 <= i < j && j < k < nums.len() && nums@[i] < nums@[j] && nums@[j] < nums@[k]
}

spec fn has_any_increasing_triplet(nums: &Vec<i32>) -> bool {
    exists|i: int, j: int, k: int| has_increasing_triplet_at(nums, i, j, k)
}
// </vc-helpers>

// <vc-spec>
fn increasing_triplet(nums: &Vec<i32>) -> (result: bool)
    ensures
        result ==> exists|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k],
        !result ==> forall|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed vector indexing to use @ operator throughout */
    let len = nums.len();
    if len < 3 {
        return false;
    }
    
    for i in 0..len - 2
        invariant
            len == nums.len(),
            len >= 3,
            forall|ii: int, jj: int, kk: int| 0 <= ii < jj && jj < kk < i ==> !(nums@[ii] < nums@[jj] && nums@[jj] < nums@[kk])
    {
        for j in (i + 1)..(len - 1)
            invariant
                len == nums.len(),
                len >= 3,
                i < len - 2,
                forall|ii: int, jj: int, kk: int| 0 <= ii < jj && jj < kk < i ==> !(nums@[ii] < nums@[jj] && nums@[jj] < nums@[kk]),
                forall|kk: int| i + 1 <= kk < j ==> !(nums@[i] < nums@[kk] && nums@[kk] < nums@[kk + 1])
        {
            for k in (j + 1)..len
                invariant
                    len == nums.len(),
                    len >= 3,
                    i < len - 2,
                    j < len - 1,
                    forall|ii: int, jj: int, kk: int| 0 <= ii < jj && jj < kk < i ==> !(nums@[ii] < nums@[jj] && nums@[jj] < nums@[kk]),
                    forall|kk: int| j + 1 <= kk < k ==> !(nums@[i] < nums@[j] && nums@[j] < nums@[kk])
            {
                if nums[i] < nums[j] && nums[j] < nums[k] {
                    return true;
                }
            }
        }
    }
    
    false
}
// </vc-code>

}
fn main() {}