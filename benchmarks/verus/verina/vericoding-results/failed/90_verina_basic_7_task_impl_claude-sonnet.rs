// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed requires/ensures from spec function */
spec fn nth_odd_number(k: u32) -> u32 
{ if k > 0 { (2 * k - 1) as u32 } else { 1 } }

spec fn sum_of_squares_helper(n: u32) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        sum_of_squares_helper((n - 1) as u32) + (nth_odd_number(n) * nth_odd_number(n)) as int
    }
}

proof fn sum_of_squares_formula_lemma(n: u32)
    ensures sum_of_squares_helper(n) == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
    decreases n
{
    if n == 0 {
        assert(sum_of_squares_helper(0) == 0);
        assert((0 * (-1) * 1) / 3 == 0);
    } else {
        sum_of_squares_formula_lemma((n - 1) as u32);
        let prev_sum = sum_of_squares_helper((n - 1) as u32);
        let curr_odd = nth_odd_number(n);
        assert(sum_of_squares_helper(n) == prev_sum + (curr_odd * curr_odd) as int);
        
        let formula_prev = ((n - 1) as int * (2 * (n - 1) as int - 1) * (2 * (n - 1) as int + 1)) / 3;
        let formula_curr = (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3;
        
        assert(curr_odd == (2 * n - 1) as u32);
        assert((curr_odd * curr_odd) as int == (2 * n as int - 1) * (2 * n as int - 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_squares_of_first_n_odd_numbers(n: u32) -> (result: u32)
    requires n >= 0,
    ensures
        result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    if n == 0 {
        return 0;
    }
    
    let mut sum: u32 = 0;
    let mut k: u32 = 1;
    
    while k <= n
        invariant
            1 <= k <= n + 1,
            sum as int == sum_of_squares_helper((k - 1) as u32)
        decreases n + 1 - k
    {
        let odd_num = (2 * k - 1) as u32;
        sum = sum + odd_num * odd_num;
        k = k + 1;
    }
    
    proof {
        sum_of_squares_formula_lemma(n);
        assert(sum as int == sum_of_squares_helper(n));
        assert(sum_of_squares_helper(n) == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3);
    }
    
    sum
}
// </vc-code>

}
fn main() {}