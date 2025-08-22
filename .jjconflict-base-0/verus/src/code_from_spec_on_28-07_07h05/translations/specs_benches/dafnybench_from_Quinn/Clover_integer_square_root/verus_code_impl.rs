use vstd::prelude::*;

verus! {
    fn square_root(n: u32) -> (r: u32)
        requires n <= 100
        ensures 
            r * r <= n,
            n < (r + 1) * (r + 1),
    {
        let mut candidate = 0u32;
        /* code modified by LLM (iteration 4): Fixed loop condition and invariants to ensure postconditions are met */
        while candidate <= 9 && (candidate + 1) * (candidate + 1) <= n
            invariant 
                candidate <= 10,
                candidate * candidate <= n,
            decreases 10 - candidate
        {
            candidate = candidate + 1;
        }
        candidate
    }
}

fn main() {}