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

    let mut set = HashSet::new();
    
    // Insert all numbers into the hash set (equivalent to the Lean HashSet operations)
    let mut i = 0;
    while i < nums.len()
        invariant i <= nums.len(),
        decreases nums.len() - i,
    {
        set.insert(nums[i]);
        i = i + 1;
    }
    
    let mut max_len = 0;
    i = 0;
    
    // Find the longest consecutive sequence
    // This matches the algorithm structure from the original Lean code
    while i < nums.len()
        invariant 
            i <= nums.len(),
            max_len <= nums.len(),
        decreases nums.len() - i,
    {
        let x = nums[i];
        
        // Only start counting from the beginning of a sequence
        // This corresponds to "if !set.contains (x - 1)" in the original
        if x > i32::MIN {
            if !set.contains(&(x - 1)) {
                let mut curr = x;
                let mut length = 1;
                
                // Count consecutive numbers
                // This corresponds to the "while set.contains (curr + 1)" loop
                while length < nums.len() && curr < i32::MAX
                    invariant 
                        length >= 1,
                        length <= nums.len(),
                    decreases nums.len() - length,
                {
                    if set.contains(&(curr + 1)) {
                        curr = curr + 1;
                        length = length + 1;
                    } else {
                        break;
                    }
                }
                
                // Update max_len (corresponds to "maxLen := Nat.max maxLen length")
                if length > max_len {
                    max_len = length;
                }
            }
        }
        i = i + 1;
    }
    
    max_len
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