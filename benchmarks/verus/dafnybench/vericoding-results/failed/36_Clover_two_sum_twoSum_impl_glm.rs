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
    let n = nums.len() as int;
    let mut i: int = 0;
    let mut j: int = 0;

    while i < n - 1
        invariant 
            0 <= i < n,
            forall|ii: int| #![trigger nums[ii as usize]] 0 <= ii < i ==> forall|jj: int| #![trigger nums[jj as usize]] ii < jj < n ==> nums[ii as usize] + nums[jj as usize] != target,
    {
        j = i + 1;
        while j < n
            invariant
                i < j <= n,
                forall|jj: int| #![trigger nums[jj as usize]] i < jj < j ==> nums[i as usize] + nums[jj as usize] != target,
        {
            if nums[i as usize] + nums[j as usize] == target {
                return (i as usize, j as usize);
            }
            j = j + 1;
        }
        i = i + 1;
    }

    assert(false);
    (0, 0)
}
// </vc-code>

fn main() {}

}