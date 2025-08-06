use vstd::prelude::*;

verus! {
    fn max(a: i32, b: i32) -> (c: i32)
        ensures c >= a && c >= b
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    fn testing() {
    // TODO: Remove this comment and implement the function body
    }
}

fn main() {}