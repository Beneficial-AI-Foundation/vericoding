/*
Based on this Rust program.
https://github.com/TheAlgorithms/Rust/blob/master/src/backtracking/permutations.rs

Verus does not support "continue", "for", !vec, and clone.
So, I refactored the original code accordingly.

Spec and loop invariants are added to prove no buffer overflow.

No spec/invariant is needed to prove no arithmetic under/overflow.
*/

/*
The permutations problem involves finding all possible permutations
of a given collection of distinct integers. For instance, given [1, 2, 3],
the goal is to generate permutations like
 [1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], and [3, 2, 1].
 This implementation uses a backtracking algorithm to generate all possible permutations.
*/
  
use vstd::prelude::*;

 
verus!{

    fn main() {
        // Example usage of the permutation function
        let nums = vec![1, 2, 3];
        let perms = permute(nums);
    }

    #[verifier::external_body]
    fn myVecClone(v: &Vec<i32>) -> Vec<i32> {
        v.clone()
    }

    pub fn permute(nums: Vec<i32>) -> Vec<Vec<i32>> {
        let mut result = Vec::new();
        let mut current_permutation = Vec::new();
        let mut used = Vec::new();
        
        // Initialize used vector with false values
        let mut i = 0;
        while i < nums.len()
        invariant
            i <= nums.len(),
            used.len() == i,
        {
            used.push(false);
            i = i + 1;
        }
        
        backtrack(&nums, &mut current_permutation, &mut used, &mut result);
        result
    }

    fn backtrack(
        nums: &Vec<i32>,
        current_permutation: &mut Vec<i32>,
        used: &mut Vec<bool>,
        result: &mut Vec<Vec<i32>>,
    ) 
    requires
        nums.len() == old(used).len(),
    ensures
        used.len() == old(used).len(),    
    {
        // Base case: if current permutation is complete
        if current_permutation.len() == nums.len() {
            let perm_clone = myVecClone(current_permutation);
            result.push(perm_clone);
            return;
        }
        
        // Try each unused number
        let mut i = 0;
        while i < nums.len()
        invariant
            i <= nums.len(),
            nums.len() == used.len(),
            current_permutation.len() <= nums.len(),
        {
            if !used[i] {
                // Choose
                used.set(i, true);
                current_permutation.push(nums[i]);
                
                // Explore
                backtrack(nums, current_permutation, used, result);
                
                // Unchoose (backtrack)
                current_permutation.pop();
                used.set(i, false);
            }
            i = i + 1;
        }
    }
}