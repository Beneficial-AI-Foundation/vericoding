use vstd::prelude::*;

verus! {

// <vc-helpers>
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
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < nums.len()
        invariant
            i <= nums.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result[j] == nums[j] * nums[j] * nums[j],
        decreases nums.len() - i
    {
        let num_val = nums[i];
        proof {
            assert(i32::MIN <= num_val * num_val <= i32::MAX);
            assert(i32::MIN <= num_val * num_val * num_val <= i32::MAX);
        }
        let square = num_val * num_val;
        let cube = square * num_val;
        result.push(cube);
        i = i + 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}