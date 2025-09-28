use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn twoSum(nums: &[i32], target: i32) -> (result: (usize, usize))
    requires 
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures 
        0 <= result.0 < result.1 < nums.len() && nums[result.0 as int] + nums[result.1 as int] == target
        && forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < result.0 && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target
        && forall|jj: int| #![trigger nums[jj]] result.0 < jj < result.1 ==> nums[result.0 as int] + nums[jj] != target,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < nums.len() - 1
        invariant
            0 <= i < nums.len(),
            forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] 
                (0 <= ii < i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
        decreases nums.len() - 1 - i,
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                i + 1 <= j <= nums.len(),
                0 <= i < nums.len() - 1,
                forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] 
                    (0 <= ii < i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
                forall|jj: int| #![trigger nums[jj]] 
                    (i < jj < j) ==> nums[i as int] + nums[jj] != target,
            decreases nums.len() - j,
        {
            if nums[i] + nums[j] == target {
                assert(nums[i as int] + nums[j as int] == target);
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // This point should be unreachable due to the precondition
    proof {
        assert(exists|ii: int, jj: int| 0 <= ii < jj < nums.len() && nums[ii] + nums[jj] == target);
        assert(forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] 
            (0 <= ii < nums.len() - 1 && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target);
        assert(false);
    }
    (0, 1)
}
// </vc-code>

fn main() {}

}