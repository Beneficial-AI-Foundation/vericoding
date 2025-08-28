use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn safe_cube(x: i32) -> bool {
    i32::MIN <= x * x * x <= i32::MAX
}

spec fn cube_value(x: i32) -> i32 
    requires safe_cube(x)
{
    x * x * x
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
            forall|k: int| #![auto] 0 <= k < i ==> cubed@[k] == nums@[k] * nums@[k] * nums@[k],
            forall|k: int| 0 <= k < nums.len() ==> (i32::MIN <= nums@[k] * nums@[k] * nums@[k] <= i32::MAX),
        decreases nums.len() - i
    {
        proof {
            assert(0 <= i < nums.len());
            assert(i32::MIN <= nums@[i] * nums@[i] * nums@[i] <= i32::MAX);
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