use vstd::prelude::*;

verus! {
    fn sum(N: u32) -> (s: u32)
        requires N >= 0,
        ensures s == N * (N + 1) / 2,
    {
        let mut result: u32 = 0;
        let mut i: u32 = 1;
        
        while i <= N
            invariant 
                1 <= i <= N + 1,
                result == (i - 1) * i / 2,
        {
            result = result + i;
            i = i + 1;
        }
        
        result
    }
}

fn main() {}