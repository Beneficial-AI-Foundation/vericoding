use vstd::prelude::*;

verus! {
    fn triple(x: i32) -> (r: i32)
        requires 
            -715827882 <= x <= 715827882,  // i32::MAX / 3 approximately
        ensures r == 3 * x
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}