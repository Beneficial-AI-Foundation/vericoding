use vstd::prelude::*;

verus! {
    fn compute_is_even(x: u32) -> (is_even: bool)
        ensures (x % 2 == 0) == is_even
    {
    return false;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}