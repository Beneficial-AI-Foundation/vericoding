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
        let x = max(5, 3);
        let y = max(-2, 10);
        let z = max(0, 0);
    }
}

fn main() {}