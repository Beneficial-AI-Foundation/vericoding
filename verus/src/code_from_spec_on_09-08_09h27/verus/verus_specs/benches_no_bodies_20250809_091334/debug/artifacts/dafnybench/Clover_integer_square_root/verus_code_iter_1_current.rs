use vstd::prelude::*;

verus! {
    fn square_root(n: u32) -> (r: u32)
        requires n <= 100
        ensures 
            r * r <= n,
            n < (r + 1) * (r + 1),
    {
        let mut i = 0;
        while i <= 10
            invariant
                i <= 11,
                i * i <= n,
        {
            if (i + 1) * (i + 1) > n {
                return i;
            }
            i = i + 1;
        }
        i
    }
}

fn main() {}