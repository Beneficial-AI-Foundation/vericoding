use vstd::prelude::*;

verus! {
    //IMPL triple
    fn triple(x: i32) -> (r: i32)
        requires 
            -715827882 <= x <= 715827882,  // i32::MAX / 3 approximately
        ensures r == 3 * x
    {
        3 * x
    }
}

fn main() {}