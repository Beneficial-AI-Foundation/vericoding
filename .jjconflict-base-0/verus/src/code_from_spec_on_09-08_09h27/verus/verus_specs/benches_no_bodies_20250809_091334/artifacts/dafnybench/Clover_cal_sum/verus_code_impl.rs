use vstd::prelude::*;

verus! {
    fn sum(N: u32) -> (s: u32)
        requires N >= 0,
        ensures s == N * (N + 1) / 2,
    {
        let mut sum = 0u32;
        let mut i = 1u32;
        
        /* code modified by LLM (iteration 1): Added decreases clause and fixed loop invariant */
        while i <= N
            invariant
                sum == (i - 1) * i / 2,
                1 <= i <= N + 1,
            decreases N + 1 - i,
        {
            sum = sum + i;
            i = i + 1;
        }
        
        sum
    }
}

fn main() {}