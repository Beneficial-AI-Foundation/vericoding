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
    let mut i: usize = 0;
    let mut found_mut: bool = false;

    while i < n && !found_mut
        invariant
            i <= n,
            (found_mut ==> exists|ii: usize, jj: usize|
                ii < jj && jj < n && #[trigger] (nums[ii] + nums[jj] == target)),
            (!found_mut ==> forall|a: usize, b: usize|
                a < b && b < n && a < i ==> #[trigger] (nums[a] + nums[b] != target))
    {
        let mut j: usize = i + 1;
        while j < n && !found_mut
            invariant
                i < n,
                i + 1 <= j && j <= n,
                (found_mut ==> exists|ii: usize, jj: usize|
                    ii < jj && jj < n && #[trigger] (nums[ii] + nums[jj] == target)),
                (!found_mut ==> forall|a: usize, b: usize|
                    a < b && b < n && (a < i || (a == i && b < j)) ==> #[trigger] (nums[a] + nums[b] != target))
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
        let n_int: int = (n as int);
        if found_mut {
            // From the loop invariant we have an existential witness (usize),
            // which gives the required existence in int indices by casting.
            assert(exists|ii: int, jj: int|
                0 <= ii < jj < n_int &&
                #[trigger] (nums[(ii as usize)] + nums[(jj as usize)] == target));
        } else {
            // From the loop invariant we have that no pair of usize indices yields target;
            // therefore no pair of int indices does either.
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