// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(n: int) -> bool {
        n >= 1
    }
    
    spec fn worst_case_presses(n: int) -> int
        recommends valid_input(n)
    {
        n * (n * n + 5) / 6
    }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [fixed compilation errors by using correct V-std library paths and lemma names] */
proof fn lemma_worst_case_formula_divisible(n: int)
    requires
        n >= 1,
    ensures
        (n * (n * n + 5)) % 6 == 0,
{
    // We show n * (n*n + 5) is divisible by 6 by rewriting it
    // as (n-1)n(n+1) + 6n. The first term is a product of 3
    // consecutive integers, so it's divisible by 3! = 6.
    // The second term is also divisible by 6.
    assert(n * (n * n + 5) == (n - 1) * n * (n + 1) + 6 * n) by(nonlinear_arith);

    let term1 = (n - 1) * n * (n + 1);
    let term2 = 6 * n;

    // Prove that 3! = 6
    vstd::math::factorial::lemma_factorial_of_n_is_computed(3);

    // Prove that the product of 3 consecutive integers is divisible by 3!
    vstd::math::lemmas::lemma_product_of_n_consecutive_ints_divisible_by_factorial_n(3, n - 1);
    
    assert(term1 % 6 == 0);

    assert(term2 % 6 == 0);
    
    // If term1 and term2 are divisible by 6, their sum is also divisible by 6.
    vstd::arithmetic::div_mod::lemma_mod_add(term1, term2, 6);
    assert((term1 + term2) % 6 == 0);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == worst_case_presses(n as int) && result as int >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [no changes, as compilation errors were in the helper] */
    let n_val = n as i32;
    
    proof {
        lemma_worst_case_formula_divisible(n as int);
    }
    
    let numerator = n_val * (n_val * n_val + 5);
    let result_val = numerator / 6;
    
    result_val as i8
}
// </vc-code>


}

fn main() {}