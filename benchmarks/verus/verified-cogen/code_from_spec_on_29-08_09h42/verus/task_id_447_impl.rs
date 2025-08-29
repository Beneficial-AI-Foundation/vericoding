use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn safe_cube(x: i32) -> int
    requires i32::MIN <= x * x * x <= i32::MAX
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
    
    /* code modified by LLM (iteration 5): converted loop variable to int and used preconditions for overflow safety */
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            cubed.len() == i,
            forall|j: int| 0 <= j < i ==> cubed[j] == nums[j as int] * nums[j as int] * nums[j as int],
        decreases nums.len() - i,
    {
        let num_val = nums[i];
        
        /* code modified by LLM (iteration 5): use preconditions to ensure overflow safety with correct indexing */
        proof {
            assert(0 <= i < nums.len());
            assert(i32::MIN <= nums[i as int] * nums[i as int] * nums[i as int] <= i32::MAX);
        }
        
        let cube = num_val * num_val * num_val;
        cubed.push(cube);
        i += 1;
    }
    
    cubed
}
// </vc-code>

} // verus!

fn main() {}