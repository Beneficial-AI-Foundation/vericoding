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
    // TODO: Remove this comment and implement the function body
    }

    #[verifier::external_body]
    fn myVecClone(v: &Vec<i32>) -> Vec<i32> {
    return Vec::new();  // TODO: Remove this line and implement the function body
    }

    pub fn permute(nums: Vec<i32>) -> Vec<Vec<i32>> {
    return Vec::new();  // TODO: Remove this line and implement the function body
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
    // TODO: Remove this comment and implement the function body
    }
}
