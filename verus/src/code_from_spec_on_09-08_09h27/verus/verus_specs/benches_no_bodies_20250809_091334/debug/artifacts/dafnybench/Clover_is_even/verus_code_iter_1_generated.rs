use vstd::prelude::*;

verus! {
    fn compute_is_even(x: u32) -> (is_even: bool)
        ensures (x % 2 == 0) == is_even
    {
        x % 2 == 0
    }
}

fn main() {}