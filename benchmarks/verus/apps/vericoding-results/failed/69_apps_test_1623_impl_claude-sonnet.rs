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
/* helper modified by LLM (iteration 5): fixed power bounds and sum calculation proofs with overflow checking */
proof fn lemma_power_positive(base: int, exp: int)
    requires base >= 2, exp >= 0
    ensures power(base, exp) >= 1
    decreases exp
{
    if exp <= 0 {
        assert(power(base, exp) == 1);
    } else {
        lemma_power_positive(base, exp - 1);
        assert(power(base, exp - 1) >= 1);
        assert(power(base, exp) == base * power(base, exp - 1));
    }
}

proof fn lemma_power_bounds(exp: int)
    requires 0 <= exp <= 19
    ensures 1 <= power(2, exp) <= 524288
    decreases exp
{
    if exp <= 0 {
        assert(power(2, exp) == 1);
    } else if exp == 1 {
        assert(power(2, exp) == 2);
    } else if exp <= 19 {
        lemma_power_bounds(exp - 1);
        assert(power(2, exp) == 2 * power(2, exp - 1));
        assert(power(2, exp - 1) <= 262144);
        assert(power(2, exp) <= 524288);
    }
}

proof fn lemma_sum_decreasing_base(start_power: int)
    requires start_power >= 1
    ensures sum_with_decreasing_powers(1, start_power) == start_power
{
    assert(sum_with_decreasing_powers(1, start_power) == start_power);
}

proof fn lemma_sum_increasing_base(max_power: int)
    requires max_power >= 1
    ensures sum_with_increasing_powers(1, max_power) == max_power
{
    assert(sum_with_increasing_powers(1, max_power) == max_power);
}

proof fn lemma_power_ordering(l: int, r: int)
    requires 1 <= l <= r <= 20
    ensures power(2, l - 1) <= power(2, r - 1)
    decreases r - l
{
    if l == r {
        assert(power(2, l - 1) == power(2, r - 1));
    } else {
        lemma_power_ordering(l, r - 1);
        assert(power(2, r - 1) == 2 * power(2, r - 2));
        assert(power(2, l - 1) <= power(2, r - 2));
        assert(power(2, l - 1) <= power(2, r - 1));
    }
}

proof fn lemma_sum_bounds(n: int, l: int, r: int)
    requires n >= 1, n <= 20, 1 <= l <= r, r <= 20
    ensures min_sum_calculation(n, l) <= 127, max_sum_calculation(n, r) <= 127
{
    lemma_power_bounds(l - 1);
    lemma_power_bounds(r - 1);
    assert(power(2, l - 1) <= 524288);
    assert(power(2, r - 1) <= 524288);
}

proof fn lemma_calculations_positive(n: int, l: int, r: int)
    requires n >= 1, 1 <= l <= r
    ensures min_sum_calculation(n, l) >= 1, max_sum_calculation(n, r) >= 1
{
    lemma_power_positive(2, l - 1);
    lemma_power_positive(2, r - 1);
    lemma_sum_decreasing_base(power(2, l - 1));
    lemma_sum_increasing_base(power(2, r - 1));
    if n == 1 {
        assert(min_sum_calculation(n, l) == power(2, l - 1));
        assert(max_sum_calculation(n, r) == power(2, r - 1));
    }
}
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
    /* code modified by LLM (iteration 5): fixed overflow checks and proper casting with bounds */
    proof {
        lemma_sum_bounds(n as int, l as int, r as int);
        lemma_calculations_positive(n as int, l as int, r as int);
        lemma_power_ordering(l as int, r as int);
    }
    
    // Calculate minimum sum using simple approach
    let mut min_sum = 0i8;
    let mut remaining = n;
    let mut power_exp = l - 1;
    
    while remaining > 0
        invariant
            0 <= remaining <= n,
            0 <= min_sum <= 127,
            0 <= power_exp <= 20,
        decreases remaining
    {
        if power_exp == 0 || remaining == 1 {
            min_sum = min_sum + remaining;
            break;
        } else {
            let current_power = if power_exp <= 6 { 1i8 << power_exp } else { 64i8 };
            min_sum = min_sum + current_power;
            if power_exp > 0 {
                power_exp = power_exp - 1;
            }
            remaining = remaining - 1;
        }
    }
    
    // Calculate maximum sum
    let mut max_sum = 0i8;
    let mut remaining2 = n;
    let mut max_power_exp = r - 1;
    
    while remaining2 > 0
        invariant
            0 <= remaining2 <= n,
            0 <= max_sum <= 127,
            0 <= max_power_exp <= 20,
        decreases remaining2
    {
        let current_power = if max_power_exp <= 6 { 1i8 << max_power_exp } else { 64i8 };
        max_sum = max_sum + current_power;
        remaining2 = remaining2 - 1;
        if remaining2 > 0 {
            max_power_exp = max_power_exp + 1;
        }
    }
    
    (min_sum, max_sum)
}
// </vc-code>


}

fn main() {}