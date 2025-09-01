use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    let n_int: int = n as int;
    let mut i: int = 0;
    let mut found_mut: bool = false;

    while i < n_int && !found_mut
        invariant
            0 <= i && i <= n_int,
            (found_mut ==> exists|ii: int, jj: int|
                0 <= ii < jj && jj < n_int && #[trigger] (nums[(ii as usize)] + nums[(jj as usize)] == target)),
            (!found_mut ==> forall|a: int, b: int|
                0 <= a < b && b < n_int && a < i ==> #[trigger] (nums[(a as usize)] + nums[(b as usize)] != target))
    {
        let mut j: int = i + 1;
        while j < n_int && !found_mut
            invariant
                0 <= i && i < n_int,
                i + 1 <= j && j <= n_int,
                (found_mut ==> exists|ii: int, jj: int|
                    0 <= ii < jj && jj < n_int && #[trigger] (nums[(ii as usize)] + nums[(jj as usize)] == target)),
                (!found_mut ==> forall|a: int, b: int|
                    0 <= a < b && b < n_int && (a < i || (a == i && b < j)) ==> #[trigger] (nums[(a as usize)] + nums[(b as usize)] != target))
        {
            if nums[(i as usize)] + nums[(j as usize)] == target {
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
                0 <= ii < jj < n_int &&
                #[trigger] (nums[(ii as usize)] + nums[(jj as usize)] == target));
        } else {
            assert(!exists|ii: int, jj: int|
                0 <= ii < jj < n_int &&
                #[trigger] (nums[(ii as usize)] + nums[(jj as usize)] == target));
        }
    }

    found_mut
    // impl-end
}
// </vc-code>

fn main() {}
}