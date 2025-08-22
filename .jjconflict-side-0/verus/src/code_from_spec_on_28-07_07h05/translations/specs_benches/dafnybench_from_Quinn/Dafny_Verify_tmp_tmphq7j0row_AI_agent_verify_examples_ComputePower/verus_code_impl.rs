use vstd::prelude::*;

verus! {
    spec fn power(n: nat) -> nat
        decreases n
    {
        if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
    }

    /* code modified by LLM (iteration 2): added helper lemma to prove power bounds */
    proof fn power_bound_lemma(n: nat)
        requires n <= 30
        ensures power(n) <= 0x40000000  // 2^30
        decreases n
    {
        if n == 0 {
            // power(0) = 1 <= 2^30
        } else {
            power_bound_lemma((n - 1) as nat);
            // power(n) = 2 * power(n-1) <= 2 * 2^29 = 2^30
        }
    }

    //IMPL compute_power
    fn compute_power(n: u32) -> (y: u32)
        requires n <= 30,
        ensures y == power(n as nat),
        decreases n
    {
        if n == 0 {
            1
        } else {
            /* code modified by LLM (iteration 2): recursive call with proper bounds checking */
            let prev = compute_power(n - 1);
            /* code modified by LLM (iteration 2): establish power relationship */
            assert(prev == power((n - 1) as nat));
            assert(power(n as nat) == 2 * power((n - 1) as nat));
            
            /* code modified by LLM (iteration 3): wrap ghost code calls in proof block */
            proof {
                power_bound_lemma(n as nat);
                power_bound_lemma((n - 1) as nat);
            }
            
            /* code modified by LLM (iteration 2): assert specific bounds for overflow safety */
            assert(power((n - 1) as nat) <= 0x20000000); // 2^29
            assert(prev <= 0x20000000);
            
            /* code modified by LLM (iteration 2): safe multiplication with proven bounds */
            let result = 2 * prev;
            result
        }
    }
}

fn main() {}