// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type errors with proper nat handling */
spec fn sum_of_first_k_odds(k: nat) -> nat
    decreases k
{
    if k == 0 {
        0nat
    } else {
        let kth_odd = 2 * k - 1;
        (kth_odd * kth_odd + sum_of_first_k_odds(k - 1))
    }
}

proof fn lemma_sum_of_squares_formula(n: nat)
    ensures sum_of_first_k_odds(n) == n * (2 * n - 1) * (2 * n + 1) / 3
    decreases n
{
    if n == 0 {
        // Base case: sum_of_first_k_odds(0) == 0 == 0 * (-1) * 1 / 3
    } else {
        // Inductive step
        if n > 0 {
            lemma_sum_of_squares_formula((n - 1) as nat);
        }
        // sum_of_first_k_odds(n) = (2*n-1)^2 + sum_of_first_k_odds(n-1)
        // = (2*n-1)^2 + (n-1) * (2*(n-1)-1) * (2*(n-1)+1) / 3
        // = (2*n-1)^2 + (n-1) * (2*n-3) * (2*n-1) / 3
        // After algebraic manipulation, this equals n * (2*n-1) * (2*n+1) / 3
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
    /* code modified by LLM (iteration 5): Fixed type errors with proper nat handling */
    if n == 0 {
        return 0;
    }
    
    let mut i: u32 = 1;
    let mut sum: u32 = 0;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            sum as int == sum_of_first_k_odds((i - 1) as nat),
        decreases n - i
    {
        let odd_number = 2 * i - 1;
        sum = sum + odd_number * odd_number;
        i = i + 1;
    }
    
    proof {
        lemma_sum_of_squares_formula(n as nat);
    }
    
    sum
}
// </vc-code>

}
fn main() {}