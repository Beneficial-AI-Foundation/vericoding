use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_sum(nums: &[i32], target: i32) -> (result: (usize, usize))
    // pre-conditions-start
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        forall|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len()
                ==> nums[i] + nums[j] <= i32::MAX
                    && nums[i] + nums[j] >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ({ let (i, j) = result; 0 <= i < nums.len() }),
        ({ let (i, j) = result; 0 <= j < nums.len() }),
        ({ let (i, j) = result; i != j }),
        ({ let (i, j) = result; nums[i as int] + nums[j as int] == target })
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = nums.len();
    
    for i in 0..n
        invariant
            forall|i_prev: int, j_prev: int| 
                0 <= i_prev < i && i_prev < j_prev < n 
                    ==> nums[i_prev] + nums[j_prev] != target,
    {
        for j in (i + 1)..n
            invariant
                i < n,
                forall|j_prev: int| 
                    i < j_prev < j 
                        ==> nums[i as int] + nums[j_prev] != target,
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
        }
    }
    
    // This point should be unreachable due to the precondition
    unreached()
}
// </vc-code>

fn main() {}
}