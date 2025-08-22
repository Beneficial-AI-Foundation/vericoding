use vstd::prelude::*;

verus! {
    fn main_method(n: i32, k: i32) -> (k_out: i32)
        requires 
            n > 0,
            k > n,
            n <= 100,    
            k <= 200,
        ensures 
            k_out >= 0,
    {
        0
    }
}

fn main() {}