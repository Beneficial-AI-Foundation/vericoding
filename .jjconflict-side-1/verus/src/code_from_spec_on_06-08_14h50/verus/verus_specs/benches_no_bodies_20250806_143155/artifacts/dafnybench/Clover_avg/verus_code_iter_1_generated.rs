use vstd::prelude::*;

verus! {
    fn compute_avg(a: u32, b: u32) -> (avg: u32)
        requires a < 0x80000000 && b < 0x80000000  // prevent overflow
        ensures avg == (a + b) / 2
    {
        (a + b) / 2
    }
}

fn main() {}