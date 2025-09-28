// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed invalid `use` statement that caused compilation error. */
spec fn pow4(base: int) -> int {
    base * base * base * base
}

spec fn sum_formula(n: int) -> int {
    if n <= 0 {
        0
    } else {
        n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
    }
}

proof fn sum_induction_lemma(i: int)
    requires
        i > 0,
    ensures
        sum_formula(i) == sum_formula(i - 1) + pow4(2 * i - 1),
{
    assert(sum_formula(i) == sum_formula(i - 1) + pow4(2 * i - 1)) by(nonlinear_arith);
}
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: i32) -> (sum: i32)
    requires n > 0,
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): No logical changes; focused on helper compilation error. */
    let mut sum: i128 = 0;
    let mut i: i128 = 1;
    let n_128 = n as i128;

    while i <= n_128
        invariant
            n > 0,
            n_128 == (n as int),
            1 <= i <= n_128 + 1,
            sum as int == sum_formula((i - 1) as int),
        decreases n_128 - i
    {
        proof {
            sum_induction_lemma(i as int);
        }
        let odd = 2 * i - 1;
        let term = odd * odd * odd * odd;
        sum = sum + term;
        i = i + 1;
    }
    sum as i32
}
// </vc-code>

}
fn main() {}