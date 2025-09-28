// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int) -> bool {
    1 <= n <= 100 && 1 <= m <= n && m <= 5
}

spec fn power(base: int, exp: int) -> int
    decreases exp when exp >= 0
{
    if exp <= 0 { 1 } else { base * power(base, exp - 1) }
}

spec fn expected_time(n: int, m: int) -> int {
    (1900 * m + 100 * (n - m)) * power(2, m)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed int literal type issues */
fn lemma_power_positive(base: int, exp: int)
    requires base > 0, exp >= 0
    ensures power(base, exp) > 0
    decreases exp
{
    if exp > 0int {
        lemma_power_positive(base, exp - 1int);
    }
}

fn lemma_power_bounds(exp: int)
    requires 0 <= exp <= 5
    ensures 1 <= power(2, exp) <= 32
    decreases exp
{
    if exp > 0int {
        lemma_power_bounds(exp - 1int);
    }
}

fn compute_power(exp: i8) -> (result: i8)
    requires 0 <= exp <= 5
    ensures result as int == power(2, exp as int)
{
    proof {
        lemma_power_bounds(exp as int);
    }
    let mut result = 1i8;
    let mut i = 0i8;
    while i < exp
        invariant
            0 <= i <= exp,
            result as int == power(2, i as int)
        decreases exp - i
    {
        result = result * 2;
        i = i + 1;
        proof {
            assert(power(2, i as int) == 2 * power(2, (i - 1) as int));
        }
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires valid_input(n as int, m as int)
    ensures result as int == expected_time(n as int, m as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute expected time formula */
    let power_2_m = compute_power(m);
    let term1 = 1900 * m * power_2_m;
    let term2 = 100 * (n - m) * power_2_m;
    term1 + term2
}
// </vc-code>


}

fn main() {}