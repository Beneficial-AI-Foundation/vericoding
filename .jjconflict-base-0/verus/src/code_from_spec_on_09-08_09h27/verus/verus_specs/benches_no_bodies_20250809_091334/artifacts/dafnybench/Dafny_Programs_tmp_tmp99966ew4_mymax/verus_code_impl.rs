use vstd::prelude::*;

verus! {
    fn max(a: i32, b: i32) -> (c: i32)
        ensures c >= a && c >= b
    {
        if a >= b {
            a
        } else {
            b
        }
    }

    fn testing() {
        // Empty implementation since no specifications are provided
    }
}

fn main() {}