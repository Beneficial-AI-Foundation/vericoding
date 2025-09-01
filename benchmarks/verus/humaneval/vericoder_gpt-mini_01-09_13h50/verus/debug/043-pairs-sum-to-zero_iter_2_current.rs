use vstd::prelude::*;

verus! {

// <vc-helpers>
// (No helpers needed)
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
    let n: int = nums.len();
    // Outer loop: iterate first index i
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant forall |p: int, q: int|
            0 <= p < q < n && p < i ==> nums[p] + nums[q] != target;
    {
        // Inner loop: iterate second index j for fixed i
        let mut j: int = i + 1;
        while j < n
            invariant 0 <= i && i <= n;
            invariant i + 1 <= j && j <= n;
            invariant forall |p: int, q: int|
                0 <= p < q < n && (p < i || (p == i && q < j)) ==> nums[p] + nums[q] != target;
        {
            if nums[i] + nums[j] == target {
                proof {
                    // Provide existential witness (i, j)
                    assert(0 <= i);
                    assert(i < j);
                    assert(j < n);
                    assert(nums[i] + nums[j] == target);
                    assert(exists |p: int, q: int| p == i && q == j && 0 <= p < q < n && nums[p] + nums[q] == target);
                }
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    proof {
        // At loop exit, i == n and invariants imply no pair sums to target
        assert(i == n);
        // From outer invariant with i == n we get no pair (p,q) with 0 <= p < q < n sums to target
        assert(!exists |p: int, q: int| 0 <= p < q < n && nums[p] + nums[q] == target);
    }
    return false;
}
// </vc-code>

fn main() {}
}