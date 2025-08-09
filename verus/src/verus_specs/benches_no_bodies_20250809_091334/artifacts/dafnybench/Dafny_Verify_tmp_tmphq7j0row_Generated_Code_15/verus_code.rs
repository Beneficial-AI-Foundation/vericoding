use vstd::prelude::*;

verus! {
    fn compute_k(n: i32, k: i32) -> (k_out: i32)
        requires 
            n > 0,
            k >= n + 1, 
            k >= 0,
            n <= 1000000,  
            k <= 1000000,
        ensures k_out >= 0,
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}