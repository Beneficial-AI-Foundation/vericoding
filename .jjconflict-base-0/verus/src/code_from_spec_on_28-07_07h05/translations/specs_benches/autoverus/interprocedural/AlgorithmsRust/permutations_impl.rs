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
        let nums = vec![1, 2, 3];
        let perms = permute(nums);
        // Example usage - in practice you might print or use the permutations
    }

    #[verifier::external_body]
    fn myVecClone(v: &Vec<i32>) -> Vec<i32> {
        v.clone()
    }

    /* code modified by LLM (iteration 1): replaced vec![false; nums.len()] with manual vector creation */
    pub fn permute(nums: Vec<i32>) -> Vec<Vec<i32>> {
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut current_permutation: Vec<i32> = Vec::new();
        let mut used: Vec<bool> = Vec::new();
        
        // Initialize used vector with false values
        let mut i = 0;
        /* code modified by LLM (iteration 2): added decreases clause to fix termination verification */
        while i < nums.len()
            invariant
                i <= nums.len(),
                used.len() == i,
            decreases nums.len() - i
        {
            used.push(false);
            i += 1;
        }
        
        backtrack(&nums, &mut current_permutation, &mut used, &mut result);
        result
    }

    /* code modified by LLM (iteration 4): fixed decreases clause to use old(current_permutation) for pre-state reference */
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
    decreases nums.len() - old(current_permutation).len()
    {
        // Base case: if current permutation is complete
        if current_permutation.len() == nums.len() {
            let cloned_perm = myVecClone(current_permutation);
            result.push(cloned_perm);
            return;
        }
        
        // Try each unused number
        let mut i = 0;
        while i < nums.len()
            invariant
                i <= nums.len(),
                nums.len() == used.len(),
                current_permutation.len() <= nums.len(),
            decreases nums.len() - i
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
            i += 1;
        }
    }
}