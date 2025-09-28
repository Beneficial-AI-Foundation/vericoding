// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_sum(nums: &[i32], target: i32) -> (result: (usize, usize))
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        forall|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len()
                ==> nums[i] + nums[j] <= i32::MAX
                    && nums[i] + nums[j] >= i32::MIN,
    ensures
        ({ let (i, j) = result; 0 <= i < nums.len() }),
        ({ let (i, j) = result; 0 <= j < nums.len() }),
        ({ let (i, j) = result; i != j }),
        ({ let (i, j) = result; nums[i as int] + nums[j as int] == target })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clauses to fix loop verification */
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < nums.len() && ii != jj ==> nums[ii] + nums[jj] != target,
        decreases nums.len() - i
    {
        let mut j: usize = 0;
        while j < nums.len()
            invariant
                j <= nums.len(),
                forall|jj: int| 0 <= jj < j && i != jj ==> nums[i as int] + nums[jj] != target,
            decreases nums.len() - j
        {
            if i != j && nums[i] + nums[j] == target {
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