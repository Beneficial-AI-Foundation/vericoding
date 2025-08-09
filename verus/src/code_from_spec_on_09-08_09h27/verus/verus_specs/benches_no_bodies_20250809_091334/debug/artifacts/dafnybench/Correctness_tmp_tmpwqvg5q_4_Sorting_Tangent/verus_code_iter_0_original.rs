use vstd::prelude::*;

verus! {
    /**
      Ather, Mohammad Faiz (s4648481/3)
      CSSE3100
      Assignment 3
      The University of Queensland
     */

    // Question 1
    fn tangent(r: Vec<i32>, x: Vec<i32>) -> (found: bool)
        requires
            true, // Simplified precondition
        ensures
            true, // Simplified postcondition
    {
    return false;  // TODO: Remove this line and implement the function body
    }

    // Author: Leino, Title: Program Proofs
    fn binary_search(a: &Vec<i32>, circle: i32) -> (n: usize)
        requires
            true, // Simplified precondition
        ensures
            0 <= n <= a.len(),
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    fn main() {
    // TODO: Remove this comment and implement the function body
    }
}