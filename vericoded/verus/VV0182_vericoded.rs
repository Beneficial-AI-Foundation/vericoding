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
/* code modified by LLM (iteration 5): fixed overflow issue by using checked_add */
{
    let mut i = 0;
    while i < nums.len() - 1
        invariant
            0 <= i <= nums.len() - 1,
            forall|k: int, l: int| 
                #![trigger nums.view()[k] + nums.view()[l]]
                0 <= k < i && k < l < nums.len() 
                ==> nums.view()[k] + nums.view()[l] != target,
            exists|i0: int, j0: int| i <= i0 < j0 < nums.len() && nums.view()[i0] + nums.view()[j0] == target,
        decreases nums.len() - i
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                i+1 <= j <= nums.len(),
                forall|l: int| i+1 <= l < j ==> nums.view()[i as int] + nums.view()[l] != target,
                forall|k: int, l: int| 
                    #![trigger nums.view()[k] + nums.view()[l]]
                    0 <= k < i && k < l < nums.len() 
                    ==> nums.view()[k] + nums.view()[l] != target,
                exists|i0: int, j0: int| i <= i0 < j0 < nums.len() && nums.view()[i0] + nums.view()[j0] == target,
            decreases nums.len() - j
        {
            if let Some(sum) = nums[i].checked_add(nums[j]) {
                if sum == target {
                    return (i, j);
                }
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        // Contradiction: loop invariant requires solution exists with i0 >= i,
        // but i = nums.len()-1 and solution requires i0 <= nums.len()-2
        assert(false);
    }
    (0, 0) // Unreachable
}
// </vc-code>

}
fn main() {}