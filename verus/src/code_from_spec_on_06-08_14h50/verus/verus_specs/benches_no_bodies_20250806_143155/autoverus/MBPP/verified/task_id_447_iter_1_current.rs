use vstd::prelude::*;

fn main() {
    let nums = vec![1, 2, 3, -2];
    let cubed = cube_element(&nums);
    println!("{:?}", cubed);
}

verus! {

fn cube_element(nums: &Vec<i32>) -> (cubed: Vec<i32>)
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                <= i32::MAX),
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                * #[trigger] nums[k] <= i32::MAX),
    ensures
        forall|i: int|
            0 <= i < nums.len() ==> cubed[i] == #[trigger] nums[i] * #[trigger] nums[i]
                * #[trigger] nums[i],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < nums.len()
        invariant
            i <= nums.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == nums[j] * nums[j] * nums[j],
    {
        let val = nums[i as usize];
        let cubed_val = val * val * val;
        result.push(cubed_val);
        i += 1;
    }
    
    result
}

} // verus!