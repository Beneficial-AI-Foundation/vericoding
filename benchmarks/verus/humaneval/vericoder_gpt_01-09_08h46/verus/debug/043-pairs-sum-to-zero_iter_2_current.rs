use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n_len = nums.len();
    let n: int = n_len as int;

    let mut i: usize = 0;
    while i < n_len
        invariant
            0 <= i as int <= n,
            forall|i0: int, j0: int|
                0 <= i0 < i as int && i0 < j0 && j0 < n ==> nums[i0 as usize] + nums[j0 as usize] != target,
        decreases n - i as int
    {
        let mut j: usize = i + 1;
        while j < n_len
            invariant
                0 <= i as int < n,
                i as int + 1 <= n,
                0 <= j as int <= n,
                i as int + 1 <= j as int,
                forall|i0: int, j0: int|
                    0 <= i0 < i as int && i0 < j0 && j0 < n ==> nums[i0 as usize] + nums[j0 as usize] != target,
                forall|j0: int| i as int < j0 && j0 < j as int ==> nums[i as usize] + nums[j0 as usize] != target,
            decreases n - j as int
        {
            if nums[i] + nums[j] == target {
                proof {
                    let ii = i as int;
                    let jj = j as int;
                    assert(0 <= ii && ii < n);
                    assert(ii + 1 <= jj);
                    assert(ii < jj);
                    assert(jj < n);
                    assert(nums[ii as usize] + nums[jj as usize] == target);
                    assert(exists|i0: int, j0: int|
                        0 <= i0 && i0 < j0 && j0 < n && nums[i0 as usize] + nums[j0 as usize] == target);
                }
                return true;
            }
            j += 1;
        }
        i += 1;
    }

    proof {
        assert(forall|i0: int, j0: int|
            0 <= i0 && i0 < j0 && j0 < n ==> nums[i0 as usize] + nums[j0 as usize] != target);
    }
    false
}
// </vc-code>

fn main() {}
}