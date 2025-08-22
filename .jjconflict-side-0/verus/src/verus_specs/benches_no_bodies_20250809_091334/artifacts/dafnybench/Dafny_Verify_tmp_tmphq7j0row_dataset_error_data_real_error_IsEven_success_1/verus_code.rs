use vstd::prelude::*;

verus! {
    spec fn even(n: int) -> bool 
        recommends n >= 0
        decreases n
    {
        if n == 0 { 
            true 
        } else if n > 0 { 
            !even(n - 1) 
        } else {
            arbitrary()
        }
    }

    fn is_even(n: u32) -> (r: bool)
        requires n >= 0,
        ensures r <==> even(n as int)
    {
    return false;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}