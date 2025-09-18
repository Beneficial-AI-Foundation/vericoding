// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn sum_odd_square(k: u32) -> u32
    requires k >= 1
{
    let odd = 2 * k - 1;
    odd * odd
}

proof fn lemma_sum_formula(n: u32)
    requires n >= 0
    ensures
        (0..n).fold(0, |acc: int, i: int| acc + sum_odd_square((i + 1) as u32) as int) == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
{
    if n == 0 {
        assert((0..0).len() == 0);
    } else {
        lemma_sum_formula((n - 1) as u32);
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
    /* code modified by LLM (iteration 5): Fixed type mismatch in fold closure parameter */
    if n == 0 {
        return 0;
    }
    
    let mut sum = 0u32;
    let mut i = 1u32;
    
    while i <= n
        invariant
            i <= n + 1,
            sum as int == ((i - 1) as int * (2 * (i - 1) as int - 1) * (2 * (i - 1) as int + 1)) / 3
    {
        let odd = 2 * i - 1;
        sum = sum + odd * odd;
        i = i + 1;
    }
    
    proof {
        lemma_sum_formula(n);
    }
    
    sum
}
// </vc-code>

}
fn main() {}