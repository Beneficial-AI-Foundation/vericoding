// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, l: int, r: int) -> bool {
    n >= 1 && l >= 1 && r >= l && r <= n && r <= 20
}

spec fn power(base: int, exp: int) -> int
    decreases exp
{
    if exp <= 0 { 1 } else { base * power(base, exp - 1) }
}

spec fn sum_with_decreasing_powers(n: int, start_power: int) -> int
    decreases n
{
    if n <= 0 { 0 } 
    else if start_power <= 1 { n }
    else { start_power + sum_with_decreasing_powers(n - 1, start_power / 2) }
}

spec fn sum_with_increasing_powers(n: int, max_power: int) -> int
    decreases n
{
    if n <= 0 { 0 }
    else if n == 1 { max_power }
    else { max_power + sum_with_increasing_powers(n - 1, max_power * 2) }
}

spec fn min_sum_calculation(n: int, l: int) -> int {
    if n >= 1 && l >= 1 {
        let start_power = power(2, l - 1);
        sum_with_decreasing_powers(n, start_power)
    } else {
        0
    }
}

spec fn max_sum_calculation(n: int, r: int) -> int {
    if n >= 1 && r >= 1 {
        let max_power = power(2, r - 1);
        sum_with_increasing_powers(n, max_power)
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_power_nonnegative(base: int, exp: int)
    requires exp >= 0
    ensures power(base, exp) >= 0
    decreases exp
{
    if exp > 0 {
        lemma_power_nonnegative(base, exp - 1);
    }
}

proof fn lemma_sum_decreasing_powers_nonnegative(n: int, start_power: int)
    requires n >= 0, start_power >= 0
    ensures sum_with_decreasing_powers(n, start_power) >= 0
    decreases n
{
    if n > 0 && start_power > 1 {
        lemma_sum_decreasing_powers_nonnegative(n - 1, start_power / 2);
    }
}

proof fn lemma_sum_increasing_powers_nonnegative(n: int, max_power: int)
    requires n >= 0, max_power >= 0
    ensures sum_with_increasing_powers(n, max_power) >= 0
    decreases n
{
    if n > 1 {
        lemma_sum_increasing_powers_nonnegative(n - 1, max_power * 2);
    }
}

proof fn lemma_min_sum_positive(n: int, l: int)
    requires valid_input(n, l, l)
    ensures min_sum_calculation(n, l) > 0
{
    let start_power = power(2, l - 1);
    lemma_power_nonnegative(2, l - 1);
    assert(start_power >= 1);
    lemma_sum_decreasing_powers_nonnegative(n, start_power);
    assert(sum_with_decreasing_powers(n, start_power) >= 1);
}

proof fn lemma_max_sum_positive(n: int, r: int)
    requires valid_input(n, r, r)
    ensures max_sum_calculation(n, r) > 0
{
    let max_power = power(2, r - 1);
    lemma_power_nonnegative(2, r - 1);
    assert(max_power >= 1);
    lemma_sum_increasing_powers_nonnegative(n, max_power);
    assert(sum_with_increasing_powers(n, max_power) >= 1);
}

/* helper modified by LLM (iteration 5): Remove ghost helper functions with fn keyword */

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, l: i8, r: i8) -> (result: (i8, i8))
    requires valid_input(n as int, l as int, r as int)
    ensures ({
        let (min_sum, max_sum) = result;
        min_sum > 0 &&
        max_sum > 0 &&
        min_sum <= max_sum &&
        min_sum as int == min_sum_calculation(n as int, l as int) &&
        max_sum as int == max_sum_calculation(n as int, r as int)
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Remove ghost function calls, use proof blocks only */
    proof {
        lemma_min_sum_positive(n as int, l as int);
        lemma_max_sum_positive(n as int, r as int);
        let min_sum_val = min_sum_calculation(n as int, l as int);
        let max_sum_val = max_sum_calculation(n as int, r as int);
        assert(min_sum_val > 0);
        assert(max_sum_val > 0);
        assert(min_sum_val <= max_sum_val);
    }
    
    // Direct calculation without ghost functions
    let min_sum_val = min_sum_calculation(n as int, l as int) as i8;
    let max_sum_val = max_sum_calculation(n as int, r as int) as i8;
    
    (min_sum_val, max_sum_val)
}
// </vc-code>


}

fn main() {}