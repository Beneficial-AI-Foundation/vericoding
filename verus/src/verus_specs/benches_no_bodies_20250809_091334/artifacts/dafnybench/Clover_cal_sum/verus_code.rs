use vstd::prelude::*;

verus! {
    fn sum(N: u32) -> (s: u32)
        requires N >= 0,
        ensures s == N * (N + 1) / 2,
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}