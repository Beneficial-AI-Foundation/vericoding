// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 2 && n % 2 == 0 && n <= 20
}

spec fn factorial(n: int) -> int
    decreases n
{
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}

spec fn expected_result(n: int) -> int {
    if valid_input(n) {
        let half = n / 2;
        let fact_n = factorial(n);
        let fact_half = factorial(half);
        let fact_half_minus_1 = factorial(half - 1);
        let binomial = fact_n / (fact_half * fact_half);
        let arrangements = fact_half_minus_1 * fact_half_minus_1;
        (binomial * arrangements) / 2
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added overflow invariants and non-zero postcondition */
fn factorial_non_ghost(n: u64) -> (result: u64)
    requires n <= 20
    ensures result != 0
{
    if n == 0 || n == 1 {
        1
    } else {
        let mut res = 1;
        let mut i = 1;
        while i < n
            invariant 1 <= i && i <= n
            invariant res == factorial(i as int) as u64
            invariant res * (i+1) <= u64::MAX
            decreases n - i
        {
            i = i + 1;
            res = res * i;
        }
        res
    }
}

fn compute_result_u64(n: u64) -> (result: u64)
    requires 2 <= n <= 20 && n % 2 == 0
{
    let half = n / 2;
    let fact_n = factorial_non_ghost(n);
    let fact_half = factorial_non_ghost(half);
    assert(fact_half != 0);
    let denominator = fact_half * fact_half;
    assert(denominator != 0);
    assert(denominator == fact_half * fact_half);
    let binomial = fact_n / denominator;
    let fact_half_minus_1 = factorial_non_ghost(half - 1);
    let arrangements = fact_half_minus_1 * fact_half_minus_1;
    (binomial * arrangements) / 2
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == expected_result(n as int) && result > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added truncate to cast and explicit bounds check */
{
    let n_u64 = n as u64;
    let result_u64 = compute_result_u64(n_u64);
    assert(result_u64 <= 127);
    let result_i8 = result_u64 as #[verifier::truncate] i8;
    result_i8
}
// </vc-code>


}

fn main() {}