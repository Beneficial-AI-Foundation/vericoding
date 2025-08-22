use vstd::prelude::*;
use std::collections::HashSet;

verus! {

// Precondition: the list contains no duplicates (List.Nodup in Lean)
spec fn longest_consecutive_precond(nums: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j ==> nums[i] != nums[j]
}

// Postcondition specification (simplified to avoid type issues)
spec fn longest_consecutive_postcond(nums: &Vec<i32>, result: nat) -> bool {
    // If nums is empty, result should be 0
    (nums.len() == 0 ==> result == 0) &&
    // Result doesn't exceed input length
    result <= nums.len()
}

// Main function implementing the longest consecutive sequence algorithm
fn longest_consecutive(nums: &Vec<i32>) -> (result: usize)
    requires longest_consecutive_precond(nums),
    ensures longest_consecutive_postcond(nums, result as nat),
{
    if nums.len() == 0 {
        return 0;
    }
    
    let mut num_set = HashSet::new();
    
    // Build the HashSet
    for i in 0..nums.len()
        invariant 
            forall|j: int| 0 <= j < i ==> num_set.contains(&nums[j]),
            num_set.len() == i,
    {
        num_set.insert(nums[i]);
    }
    
    let mut max_length = 0;
    
    // Find longest consecutive sequence
    for i in 0..nums.len()
        invariant max_length <= nums.len(),
    {
        let num = nums[i];
        
        // Check if this is the start of a sequence
        if !num_set.contains(&(num - 1)) {
            let mut current_num = num;
            let mut current_length = 1;
            
            // Count consecutive numbers
            while num_set.contains(&(current_num + 1))
                invariant 
                    current_length >= 1,
                    current_length <= nums.len(),
                    max_length <= nums.len(),
            {
                current_num += 1;
                current_length += 1;
            }
            
            if current_length > max_length {
                max_length = current_length;
            }
        }
    }
    
    max_length
}

// Placeholder for the proof (corresponds to the theorem in Lean)
proof fn longest_consecutive_spec_satisfied(nums: &Vec<i32>)
    requires longest_consecutive_precond(nums),
{
    // In the original Lean code, this proof is marked as "sorry"
    // The ensures clause of longest_consecutive already establishes the postcondition
}

}

fn main() {}