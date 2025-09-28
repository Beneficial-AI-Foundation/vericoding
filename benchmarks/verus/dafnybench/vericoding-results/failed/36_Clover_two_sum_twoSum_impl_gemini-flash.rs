use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    while i < nums.len()
        invariant 
            0 <= i <= nums.len(),
            // All pairs (k,j) with k < i have been checked
            forall|k: int, j: int| 0 <= k < i && k < j < nums.len() ==> nums[k] + nums[j] != target,
        decreases nums.len() - i
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                0 <= i,
                i < j,
                j <= nums.len(),
                // All pairs (i,k) with k < j have been checked
                (forall|k: int| (i as int) < k && k < (j as int) ==> nums[i as int] + nums[k] != target),
            decreases nums.len() - j
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    // The given problem statement guarantees a solution exists, so this part should be unreachable
    // in a correct implementation. However, Verus demands that all code paths return a value.
    // We can return a dummy value because the `requires` clause ensures a solution will be found.
    (0, 1) 
}
// </vc-code>

fn main() {}

}