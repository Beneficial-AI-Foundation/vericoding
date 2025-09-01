use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut i: usize = 0;
    while i < n - 1 {
        invariant { forall (k: int, l: int) :: (0 <= k && k < i && k < l && l < n) && #[trigger] (nums[k] + nums[l]) == target ==> false }
        let mut j: usize = i + 1;
        while j < n {
            invariant { j >= i + 1 }
            invariant { j <= n }
            invariant { forall l: int :: (i < l && l < j) && #[trigger] (nums[i] + nums[l]) == target ==> false }
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}
}