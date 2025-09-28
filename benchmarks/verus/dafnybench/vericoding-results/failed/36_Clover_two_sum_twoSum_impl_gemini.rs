// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

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
    /* code modified by LLM (iteration 2): fixed compile error by removing semicolon after unreached() */
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]]
                (0 <= ii < i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
        decreases nums.len() - i
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                i < nums.len(),
                i < j <= nums.len(),
                forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]]
                    (0 <= ii < i && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target,
                forall|jj_inner: int| #![trigger nums[jj_inner]]
                    (i < jj_inner < j) ==> nums[i as int] + nums[jj_inner] != target,
            decreases nums.len() - j
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(forall|ii: int, jj: int| 0 <= ii < nums.len() && ii < jj < nums.len() ==> nums[ii] + nums[jj] != target);
        assert(!(exists|i_ex: int, j_ex: int| 0 <= i_ex < j_ex < nums.len() && nums[i_ex] + nums[j_ex] == target));
        assert(false);
    }
    unreached()
}
// </vc-code>

}
fn main() {}