use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to prove the bounds for cubing
proof fn lemma_cube_bounds(x: i32)
    requires
        i32::MIN <= x * x <= i32::MAX,
        i32::MIN <= x * x * x <= i32::MAX,
    ensures
        i32::MIN <= x * x * x <= i32::MAX,
{
    // The ensures clause is automatically proven from the requires
}
// </vc-helpers>

// <vc-spec>
fn cube_element(nums: &Vec<i32>) -> (cubed: Vec<i32>)
    // pre-conditions-start
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                <= i32::MAX),
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                * #[trigger] nums[k] <= i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < nums.len() ==> cubed[i] == #[trigger] nums[i] * #[trigger] nums[i]
                * #[trigger] nums[i],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut cubed = Vec::new();
    let mut i = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            cubed.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] cubed[k] == nums[k] * nums[k] * nums[k],
        decreases nums.len() - i
    {
        proof {
            assert(0 <= i < nums.len());
            assert(i32::MIN <= nums[i as int] * nums[i as int] * nums[i as int] <= i32::MAX);
        }
        let cube = nums[i] * nums[i] * nums[i];
        cubed.push(cube);
        i += 1;
    }
    cubed
}
// </vc-code>

} // verus!

fn main() {}