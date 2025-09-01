use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
        invariant 0 <= i as int
        invariant i as int <= n
        invariant forall|i0: int, j0: int|
            0 <= i0 && i0 < i as int && i0 < j0 && j0 < n ==> nums[i0] + nums[j0] != target
        decreases n - i as int
    {
        let mut j: usize = i + 1;
        while j < n_len
            invariant 0 <= i as int
            invariant i as int < n
            invariant 0 <= j as int
            invariant j as int <= n
            invariant i as int + 1 <= j as int
            invariant forall|i0: int, j0: int|
                0 <= i0 && i0 < i as int && i0 < j0 && j0 < n ==> nums[i0] + nums[j0] != target
            invariant forall|j0: int| i as int < j0 && j0 < j as int ==> nums[i as int] + nums[j0] != target
            decreases n - j as int
        {
            // Prepare safe arithmetic and indexing
            proof {
                assert(0 <= i as int && i as int < j as int && j as int < n);
            }
            let a = nums[i];
            let b = nums[j];
            let sum = a + b;

            if sum == target {
                proof {
                    let ii = i as int;
                    let jj = j as int;
                    assert(0 <= ii && ii < jj && jj < n);
                    assert(nums[ii] + nums[jj] == target);
                    assert(exists|i0: int, j0: int| 0 <= i0 && i0 < j0 && j0 < n && nums[i0] + nums[j0] == target);
                }
                return true;
            } else {
                proof {
                    assert(nums[i as int] + nums[j as int] != target);
                }
                j += 1;
            }
        }

        // After finishing inner loop, all pairs with first index i are not equal to target
        proof {
            assert(forall|j0: int| i as int < j0 && j0 < n ==> nums[i as int] + nums[j0] != target);
        }

        i += 1;
    }

    // Prove that no such pair exists
    proof {
        assert(i as int == n);
        assert(forall|i0: int, j0: int| 0 <= i0 && i0 < j0 && j0 < n ==> nums[i0] + nums[j0] != target);
    }
    false
}
// </vc-code>

fn main() {}
}