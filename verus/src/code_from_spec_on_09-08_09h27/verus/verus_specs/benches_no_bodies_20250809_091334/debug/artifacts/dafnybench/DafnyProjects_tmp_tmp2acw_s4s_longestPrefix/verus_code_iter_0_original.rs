use vstd::prelude::*;

verus! {
    // MFES, Exam 8/Sept/20201, Exercise 5 

    spec fn seq_equal_prefix(a: Seq<i32>, b: Seq<i32>, len: int) -> bool {
        forall|k: int| 0 <= k < len ==> a[k] == b[k]
    }

    // Computes the length (i) of the longest common prefix (initial subarray) 
    // of two sequences a and b. 
    fn longest_prefix(a: &[i32], b: &[i32]) -> (i: usize)
        ensures 
            i <= a.len() && i <= b.len(),
            seq_equal_prefix(a@, b@, i as int),
            i < a.len() && i < b.len() ==> a@[i as int] != b@[i as int]
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
 
    // Test method with an example.
    fn test_longest_prefix() {
    // TODO: Remove this comment and implement the function body
    }

    fn main() {}
}