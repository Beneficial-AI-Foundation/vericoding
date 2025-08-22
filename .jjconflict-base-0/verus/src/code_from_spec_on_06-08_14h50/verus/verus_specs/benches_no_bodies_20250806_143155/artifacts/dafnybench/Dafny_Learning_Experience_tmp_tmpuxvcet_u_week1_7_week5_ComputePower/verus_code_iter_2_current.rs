use vstd::prelude::*;

verus! {
    spec fn power(n: nat) -> nat
        decreases n
    {
        if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
    }

    fn calc_power(n: u32) -> (p: u32)
        ensures p as nat == 2 * n
    {
        2 * n
    }

    fn compute_power(n: u32) -> (p: u32)
        ensures p as nat == power(n as nat)
    {
        let mut result: u32 = 1;
        let mut i: u32 = 0;
        
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        while i < n
            invariant 
                i <= n,
                result as nat == power(i as nat)
            decreases n - i
        {
            result = result * 2;
            i = i + 1;
        }
        
        result
    }
}

fn main() {}