use vstd::prelude::*;

fn main() {
    let nums = vec![1, 2, 3, 4];
    let squared = square_nums(&nums);
    println!("Original: {:?}", nums);
    println!("Squared: {:?}", squared);
}

verus! {

fn square_nums(nums: &Vec<i32>) -> (squared: Vec<i32>)
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
    ensures
        nums.len() == squared.len(),
        forall|k: int| 0 <= k < nums.len() ==> (#[trigger] squared[k] == nums[k] * nums[k]),
{
    let mut squared = Vec::new();
    
    for i in 0..nums.len()
        invariant
            squared.len() == i,
            forall|k: int| 0 <= k < i ==> (#[trigger] squared[k] == nums[k] * nums[k]),
    {
        let square_val = nums[i] * nums[i];
        squared.push(square_val);
    }
    
    squared
}

} // verus!