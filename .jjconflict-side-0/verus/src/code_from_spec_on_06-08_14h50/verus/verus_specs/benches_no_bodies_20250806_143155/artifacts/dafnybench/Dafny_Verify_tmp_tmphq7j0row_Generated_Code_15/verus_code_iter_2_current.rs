use vstd::prelude::*;

verus! {
    // The postcondition only requires that k_out >= 0.
    // Since k >= n + 1 and n > 0, we know that k >= 2. Also, since k >= 0 is given, 
    // we know k is non-negative. The simplest implementation that satisfies the 
    // postcondition would be to return any non-negative value.
    // Given that we have k available and k >= 0 from the preconditions, 
    // returning k itself would satisfy the postcondition k_out >= 0.

    fn compute_k(n: i32, k: i32) -> (k_out: i32)
        requires 
            n > 0,
            k >= n + 1, 
            k >= 0,
            n <= 1000000,  
            k <= 1000000,
        ensures k_out >= 0,
    {
        /* code modified by LLM (iteration 1): moved documentation text into comments and kept simple implementation returning k */
        k
    }
}

fn main() {}