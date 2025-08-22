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
        let mut i: usize = 0;
        
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        while i < a.len() && i < b.len() && a[i] == b[i]
            invariant
                i <= a.len() && i <= b.len(),
                seq_equal_prefix(a@, b@, i as int)
            decreases a.len() - i
        {
            i = i + 1;
        }
        
        i
    }
 
    // Test method with an example.
    fn test_longest_prefix() {
        let a = [1, 2, 3, 4, 5];
        let b = [1, 2, 3, 7, 8];
        let result = longest_prefix(&a, &b);
        assert(result == 3);
        
        let c = [1, 2, 3];
        let d = [1, 2, 3, 4, 5];
        let result2 = longest_prefix(&c, &d);
        assert(result2 == 3);
        
        let e = [1, 2];
        let f = [3, 4];
        let result3 = longest_prefix(&e, &f);
        assert(result3 == 0);
    }

    fn main() {}
}