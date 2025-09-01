use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall |p: int, q: int|
                #![trigger nums@[p], nums@[q]]
                0 <= p < (i as int) && p < q < nums@.len()
                && nums@[p] + nums@[q] == target ==> false
        decreases nums@.len() - (i as int)
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                i < j <= nums.len(),
                forall |k: int| 
                    #![trigger nums@[i as int], nums@[k]]
                    (i as int) < k < (j as int) ==> nums@[i as int] + nums@[k] != target
            decreases nums@.len() - (j as int)
        {
            let sum = nums[i] + nums[j];
            if sum == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    (0, 0)
}
// </vc-code>

fn main() {}
}