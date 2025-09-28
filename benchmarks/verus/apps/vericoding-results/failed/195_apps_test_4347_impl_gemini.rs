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
/* helper modified by LLM (iteration 5): No code change needed, only updated comment. */
fn exec_factorial(n: u8) -> (result: u64)
    requires n <= 20
    ensures result as int == factorial(n as int)
{
    let mut i: u8 = 1;
    let mut res: u64 = 1;
    while i <= n
        invariant
            n <= 20,
            i > 0,
            i <= n + 1,
            res as int == factorial((i - 1) as int),
    {
        res = res * (i as u64);
        i = i + 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == expected_result(n as int) && result > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected paths for binomial lemmas. */
    let n_u64 = n as u64;
    let half_u64 = n_u64 / 2;

    let fact_n = exec_factorial(n as u8);
    let fact_half = exec_factorial(half_u64 as u8);

    proof {
        let n_int = n as int;
        let half_int = n_int / 2;
        vstd::math::lemma_choose_division(n_int as nat, half_int as nat);
    }
    let binomial = fact_n / (fact_half * fact_half);

    assert(half_u64 >= 1);
    let fact_half_minus_1 = exec_factorial((half_u64 - 1) as u8);
    let arrangements = fact_half_minus_1 * fact_half_minus_1;

    let product = binomial * arrangements;

    proof {
        let n_int = n as int;
        let half_int = n_int / 2;
        assert(half_int >= 1);
        vstd::arithmetic::power2::lemma_choose_2k_k_is_even(half_int as nat);

        let spec_binomial = choose(n_int as nat, half_int as nat);
        assert(binomial as int == spec_binomial);
        assert(spec_binomial % 2 == 0);

        let spec_arrangements = factorial(half_int - 1) * factorial(half_int - 1);
        assert(arrangements as int == spec_arrangements);

        assert((product as int) % 2 == 0);
    }
    let result_u64 = product / 2;

    result_u64 as i8
}
// </vc-code>


}

fn main() {}