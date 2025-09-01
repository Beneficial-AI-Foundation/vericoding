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
    let n: int = nums.len() as int;
    let mut i: int = 0;
    let mut found_mut: bool = false;

    while i < n && !found_mut
        invariant
            0 <= i && i <= n,
            (found_mut ==> exists|ii: int, jj: int|
                0 <= ii < jj < n && #[trigger] (nums[(ii as usize)] + nums[(jj as usize)] == target)),
            (!found_mut ==> forall|a: int, b: int|
                0 <= a < b < n && a < i ==> #[trigger] (nums[(a as usize)] + nums[(b as usize)] != target))
    {
        let mut j: int = i + 1;
        while j < n && !found_mut
            invariant
                0 <= i && i < n,
                i+1 <= j && j <= n,
                (found_mut ==> exists|ii: int, jj: int|
                    0 <= ii < jj < n && #[trigger] (nums[(ii as usize)] + nums[(jj as usize)] == target)),
                (!found_mut ==> forall|a: int, b: int|
                    0 <= a < b < n && (a < i || (a == i && b < j)) ==> #[trigger] (nums[(a as usize)] + nums[(b as usize)] != target))
        {
            if nums[(i as usize)] + nums[(j as usize)] == target {
                found_mut = true;
            } else {
                j = j + 1;
            }
        }

        i = i + 1;
    }

    // At this point, either found_mut is true (and the invariant gives an example),
    // or i == n and the invariant gives that no pair exists.
    found_mut
    // impl-end
}
// </vc-code>

fn main() {}
}