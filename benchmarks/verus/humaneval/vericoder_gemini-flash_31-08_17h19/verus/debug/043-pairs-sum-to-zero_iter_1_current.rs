use vstd::prelude::*;

verus! {

// <vc-helpers>
#[macro_export]
macro_rules! array_mut_ref {
    ($arr:expr, $idx:expr) => {
        #[allow(unused_unsafe)]
        unsafe {
            vstd::slice::get_unchecked_mut($arr, $idx)
        }
    };
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn pairs_sum_to_zero(nums: &[i32], target: i32) -> (found: bool)
    // pre-conditions-start
    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j]
                >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        found <==> exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = nums.len();
    let mut i: int = 0;
    while i < n {
        let mut j: int = i + 1;
        while j < n
            invariant
                0 <= i < n,
                i + 1 <= j <= n,
                forall|idx_i: int, idx_j: int|
                    0 <= idx_i < idx_j < n && idx_i == i && idx_j < j ==> nums[idx_i] + nums[idx_j] != target,
                forall|idx_i: int, idx_j: int|
                    0 <= idx_i < n && idx_i < i ==> forall|k: int| idx_i < k < n ==> nums[idx_i] + nums[k] != target,
        {
            if nums[i as usize] + nums[j as usize] == target {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {}
}