use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>
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
    // impl-start
    let n: usize = nums.len();
    let mut i: usize = 0;
    let mut found_mut: bool = false;

    while i < n && !found_mut
        invariant
            0 <= (i as int) && (i as int) <= (n as int),
            (found_mut ==> exists|ii: int, jj: int|
                0 <= ii < jj && jj < (n as int) && #[trigger] (nums[ii] + nums[jj] == target)),
            (!found_mut ==> forall|a: int, b: int|
                0 <= a < b && b < (n as int) && a < (i as int) ==> #[trigger] (nums[a] + nums[b] != target))
    {
        let mut j: usize = i + 1;
        while j < n && !found_mut
            invariant
                0 <= (i as int) && (i as int) < (n as int),
                (i as int) + 1 <= (j as int) && (j as int) <= (n as int),
                (found_mut ==> exists|ii: int, jj: int|
                    0 <= ii < jj && jj < (n as int) && #[trigger] (nums[ii] + nums[jj] == target)),
                (!found_mut ==> forall|a: int, b: int|
                    0 <= a < b && b < (n as int) && (a < (i as int) || (a == (i as int) && b < (j as int))) ==> #[trigger] (nums[a] + nums[b] != target))
        {
            if nums[i] + nums[j] == target {
                found_mut = true;
            } else {
                j = j + 1;
            }
        }

        i = i + 1;
    }

    proof {
        if found_mut {
            assert(exists|ii: int, jj: int|
                0 <= ii < jj < (n as int) &&
                #[trigger] (nums[ii] + nums[jj] == target));
        } else {
            assert(!exists|ii: int, jj: int|
                0 <= ii < jj < (n as int) &&
                #[trigger] (nums[ii] + nums[jj] == target));
        }
    }

    found_mut
    // impl-end
}
// </vc-code>

fn main() {}
}