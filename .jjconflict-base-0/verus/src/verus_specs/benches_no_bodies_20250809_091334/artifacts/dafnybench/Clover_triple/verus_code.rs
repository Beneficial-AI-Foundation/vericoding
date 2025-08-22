use vstd::prelude::*;

verus! {
    fn triple(x: i64) -> (r: i64)
        requires -1000000 <= x <= 1000000, // prevent overflow
        ensures r == 3 * x
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}