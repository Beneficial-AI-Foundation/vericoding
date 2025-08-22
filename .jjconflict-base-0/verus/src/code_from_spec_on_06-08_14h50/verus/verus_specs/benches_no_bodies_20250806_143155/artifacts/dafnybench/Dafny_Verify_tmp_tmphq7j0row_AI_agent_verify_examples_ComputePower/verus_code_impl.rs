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
        let mut result = 1u32;
        let mut i = 0u32;
        
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        while i < n
            invariant 
                i <= n,
                result == power(i as nat),
            decreases n - i
        {
            result = result * 2;
            i = i + 1;
        }
        
        result
    }
}

fn main() {}