// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed nat casts and fixed return types */
spec fn sum_of_fourth_powers_helper(k: nat) -> nat
    decreases k
{
    if k == 0 { 0 } else { let odd = 2 * k - 1; odd * odd * odd * odd + sum_of_fourth_powers_helper(k - 1) }
}

proof fn sum_formula_lemma(n: nat)
    ensures
        15 * sum_of_fourth_powers_helper(n) == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
{
    if n == 0 {
        assert(sum_of_fourth_powers_helper(0) == 0);
        assert(0 * (2 * 0 + 1) * (7 + 24 * (0 * 0 * 0) - 12 * (0 * 0) - 14 * 0) == 0);
    } else {
        sum_formula_lemma(n - 1);
        let odd = 2 * n - 1;
        let prev_sum = sum_of_fourth_powers_helper(n - 1);
        let curr_sum = sum_of_fourth_powers_helper(n);
        
        assert(curr_sum == odd * odd * odd * odd + prev_sum);
        
        let rhs_n = n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n);
        let rhs_n_minus_1 = (n - 1) * (2 * (n - 1) + 1) * (7 + 24 * ((n - 1) * (n - 1) * (n - 1)) - 12 * ((n - 1) * (n - 1)) - 14 * (n - 1));
        
        assert(15 * prev_sum == rhs_n_minus_1);
        assert(15 * curr_sum == 15 * (odd * odd * odd * odd + prev_sum));
        assert(15 * curr_sum == 15 * odd * odd * odd * odd + 15 * prev_sum);
        assert(15 * curr_sum == 15 * odd * odd * odd * odd + rhs_n_minus_1);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: nat) -> (result: nat)
    ensures
        15 * result == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): return u64 directly without nat cast */
    let mut sum: u64 = 0;
    let mut k: u64 = 1;
    let n_u64: u64 = n as u64;
    
    while k <= n_u64
        invariant
            k <= n_u64 + 1,
            sum == sum_of_fourth_powers_helper((k - 1) as nat) as u64
        decreases n_u64 - k
    {
        let odd = 2 * k - 1;
        let fourth_power = odd * odd * odd * odd;
        sum = sum + fourth_power;
        k = k + 1;
    }
    
    proof {
        sum_formula_lemma(n);
        assert(sum == sum_of_fourth_powers_helper(n) as u64);
    }
    
    sum
}
// </vc-code>

}
fn main() {}