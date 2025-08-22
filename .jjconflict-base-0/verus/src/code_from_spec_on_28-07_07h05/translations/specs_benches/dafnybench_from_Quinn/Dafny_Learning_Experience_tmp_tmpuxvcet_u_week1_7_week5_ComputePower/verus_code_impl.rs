use vstd::prelude::*;

verus! {
    spec fn power(n: nat) -> nat
        decreases n
    {
        if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
    }

    /* code modified by LLM (iteration 1): Fixed postcondition to match power function and added overflow prevention */
    fn calc_power(n: u32) -> (p: u32)
        requires n < 32  // Prevent overflow since 2^32 doesn't fit in u32
        ensures p as nat == power(n as nat)
    {
        let mut result: u32 = 1;
        let mut i: u32 = 0;
        
        while i < n
            invariant
                0 <= i <= n,
                result as nat == power(i as nat),
                result <= 0x8000_0000,  // Ensure no overflow in next iteration
            decreases n - i
        {
            result = result * 2;
            i = i + 1;
        }
        
        result
    }

    /* code modified by LLM (iteration 1): Added overflow prevention and fixed loop invariant maintenance */
    fn compute_power(n: u32) -> (p: u32)
        requires n < 32  // Prevent overflow since 2^32 doesn't fit in u32
        ensures p as nat == power(n as nat)
    {
        let mut result: u32 = 1;
        let mut i: u32 = 0;
        
        while i < n
            invariant
                0 <= i <= n,
                result as nat == power(i as nat),
                result <= 0x8000_0000,  // Ensure no overflow in next iteration
            decreases n - i
        {
            result = result * 2;
            i = i + 1;
        }
        
        result
    }
}

fn main() {}