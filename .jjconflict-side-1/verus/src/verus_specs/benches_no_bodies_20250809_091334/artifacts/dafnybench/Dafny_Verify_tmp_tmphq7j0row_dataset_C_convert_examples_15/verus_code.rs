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
    return 0;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}