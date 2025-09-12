// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 2 && n % 2 == 0 && n <= 20
}

spec fn factorial(n: int) -> int
    decreases n
{
    if n <= 0 { 1 } else { n * factorial(n - 1) }
}

spec fn expected_result(n: int) -> int
    requires valid_input(n)
{
    let half = n / 2;
    let fact_n = factorial(n);
    let fact_half = factorial(half);
    let fact_half_minus_1 = factorial(half - 1);
    let binomial = fact_n / (fact_half * fact_half);
    let arrangements = fact_half_minus_1 * fact_half_minus_1;
    (binomial * arrangements) / 2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: int)
    requires valid_input(n)
    ensures 
        result == expected_result(n) &&
        result > 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}