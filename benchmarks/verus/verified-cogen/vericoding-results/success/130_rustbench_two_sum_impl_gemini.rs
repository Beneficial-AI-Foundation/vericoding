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
    /* code modified by LLM (iteration 3): added decreases clauses to both loops for termination */
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            nums.len() >= 2,
            0 <= i <= nums.len(),
            exists|k: int, l: int| 0 <= k < l < nums.len() && nums[k] + nums[l] == target,
            forall|k: int, l: int| 0 <= k < i && k < l < nums.len() ==> nums[k] + nums[l] != target,
            forall|k: int, l: int|
                0 <= k < nums.len() && 0 <= l < nums.len()
                    ==> nums[k] + nums[l] <= i32::MAX
                        && nums[k] + nums[l] >= i32::MIN,
        decreases nums.len() - i
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                nums.len() >= 2,
                0 <= i < nums.len(),
                i + 1 <= j <= nums.len(),
                exists|k: int, l: int| 0 <= k < l < nums.len() && nums[k] + nums[l] == target,
                forall|k: int, l: int| 0 <= k < i && k < l < nums.len() ==> nums[k] + nums[l] != target,
                forall|k: int| i < k < j ==> nums[i as int] + nums[k as int] != target,
                forall|k: int, l: int|
                    0 <= k < nums.len() && 0 <= l < nums.len()
                        ==> nums[k] + nums[l] <= i32::MAX
                            && nums[k] + nums[l] >= i32::MIN,
            decreases nums.len() - j
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