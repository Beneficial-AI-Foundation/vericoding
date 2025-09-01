use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn max_array(nums: &[i32]) -> (idx: usize)
    // pre-conditions-start
    requires
        nums.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= idx && idx < nums.len(),
        forall|i: int| 0 <= i && i < nums.len() ==> nums[i] <= nums[idx as int],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: usize = nums.len();
    let mut best: usize = 0usize;
    let mut i: usize = 1usize;
    while i < n {
        invariant i <= n;
        invariant best < n;
        invariant forall |j: int| 0 <= j && j < i as int ==> #[trigger] nums[j as usize] <= nums[best];
        {
            if nums[i] > nums[best] {
                best = i;
            }
            i = i + 1;
        }
    }
    proof {
        // from loop invariants and loop exit we get the full forall for all j < n
        assert(i == n);
        assert(forall |j: int| 0 <= j && j < n as int ==> nums[j as usize] <= nums[best]);
    }
    best
    // impl-end
}
// </vc-code>

fn main() {}
}