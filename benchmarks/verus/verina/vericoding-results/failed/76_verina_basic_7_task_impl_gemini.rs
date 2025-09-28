// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn formula(k: int) -> int {
    if k < 0 { 0 } else { k * (2 * k - 1) * (2 * k + 1) / 3 }
}

proof fn lemma_prod_divisible_by_3(n: int)
    ensures (n * (2 * n - 1) * (2 * n + 1)) % 3 == 0
{
    assert((n * (2 * n - 1) * (2 * n + 1)) % 3 == 0) by(nonlinear_arith);
}

proof fn lemma_sum_of_squares_inductive_step(i: int)
    requires i > 0,
    ensures formula(i) == formula(i-1) + (2*i-1)*(2*i-1),
{
    lemma_prod_divisible_by_3(i);
    lemma_prod_divisible_by_3(i-1);
    assert(formula(i) == formula(i-1) + (2*i-1)*(2*i-1)) by(nonlinear_arith);
}

proof fn lemma_formula_is_monotonic(i: int, j: int)
    requires
        0 <= i <= j,
    ensures
        formula(i) <= formula(j),
    decreases j - i,
{
    if i < j {
        lemma_formula_is_monotonic(i, j-1);
        assert(j > 0);
        lemma_sum_of_squares_inductive_step(j);
        assert(formula(j) >= formula(j-1));
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
    let mut i: u32 = 1;
    let mut sum: u32 = 0;
    while i <= n
        invariant
            i > 0,
            i <= n + 1,
            sum as int == formula((i-1) as int),
        decreases n - i
    {
        proof {
            if i <= n {
                lemma_formula_is_monotonic(i as int, n as int);
            }
            lemma_sum_of_squares_inductive_step(i as int);
        }

        let odd_num: u32 = 2 * i - 1;
        let square: u32 = odd_num * odd_num;
        sum = sum + square;
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}