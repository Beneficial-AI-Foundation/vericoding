use vstd::prelude::*;

verus! {
    spec fn power(n: nat) -> nat
        decreases n
    {
        if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
    }

    fn compute_power(n: u32) -> (y: u32)
        requires n <= 30,
        ensures y == power(n as nat),
    {
        /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
        let mut result: u32 = 1;
        let mut i: u32 = 0;
        
        while i < n
            invariant 
                i <= n,
                result == power(i as nat),
                n <= 30,
            decreases n - i,
        {
            result = result * 2;
            i = i + 1;
        }
        
        result
    }
}

fn main() {}