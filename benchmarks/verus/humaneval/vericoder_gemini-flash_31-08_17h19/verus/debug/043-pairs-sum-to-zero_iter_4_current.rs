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
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int && i as int <= n as int,
            forall|idx_i: int, idx_j: int|
                0 <= idx_i < idx_j < n as int && idx_i < i as int ==> nums[idx_i as usize] + nums[idx_j as usize] != target,
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                0 <= i as int && i as int < n as int,
                i as int + 1 <= j as int && j as int <= n as int,
                forall|idx_i: int, idx_j: int|
                    0 <= idx_i < idx_j < n as int && idx_i == i as int && idx_j < j as int ==> nums[idx_i as usize] + nums[idx_j as usize] != target,
                forall|idx_i: int| #[trigger] (idx_i < i as int) && (0 <= idx_i) ==> forall|k: int| #[trigger] (idx_i < k) && (k < n as int) ==> nums[idx_i as usize] + nums[k as usize] != target,
        {
            if nums[i] + nums[j] == target {
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