use vstd::prelude::*;

verus! {
    fn square_root(n: u32) -> (r: u32)
        requires n <= 100
        ensures 
            r * r <= n,
            n < (r + 1) * (r + 1),
    {
        let mut r = 0;
        while r * r <= n && (r + 1) * (r + 1) <= n
            invariant 
                r * r <= n,
                r <= 10,
        {
            r = r + 1;
        }
        r
    }
}

fn main() {}