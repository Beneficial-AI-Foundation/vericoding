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
/* helper modified by LLM (iteration 3): fixed power lemma and added bounds checking helpers */
proof fn lemma_power_positive(base: int, exp: int)
    requires base == 2
    ensures power(base, exp) > 0
    decreases exp
{
    if exp <= 0 {
        assert(power(base, exp) == 1);
    } else {
        lemma_power_positive(base, exp - 1);
        assert(power(base, exp - 1) > 0);
        assert(power(base, exp) == base * power(base, exp - 1));
        assert(base > 0);
        assert(power(base, exp) > 0);
    }
}

proof fn lemma_power_bounds(exp: int)
    requires 0 <= exp <= 19
    ensures 1 <= power(2, exp) <= 524288
    decreases exp
{
    if exp == 0 {
        assert(power(2, 0) == 1);
    } else {
        lemma_power_bounds(exp - 1);
        assert(power(2, exp) == 2 * power(2, exp - 1));
    }
}

proof fn lemma_sum_decreasing_bounds(n: int, start_power: int)
    requires
        1 <= n <= 20,
        1 <= start_power <= 524288
    ensures 
        n <= sum_with_decreasing_powers(n, start_power) <= n * start_power
    decreases n
{
    if n == 1 {
        if start_power <= 1 {
            assert(sum_with_decreasing_powers(1, start_power) == 1);
        } else {
            assert(sum_with_decreasing_powers(1, start_power) == start_power);
        }
    } else {
        if start_power <= 1 {
            assert(sum_with_decreasing_powers(n, start_power) == n);
        } else {
            lemma_sum_decreasing_bounds(n - 1, start_power / 2);
        }
    }
}

proof fn lemma_sum_increasing_bounds(n: int, max_power: int)
    requires
        1 <= n <= 20,
        1 <= max_power <= 524288
    ensures 
        max_power <= sum_with_increasing_powers(n, max_power) <= max_power * (power(2, n) - 1)
    decreases n
{
    if n == 1 {
        assert(sum_with_increasing_powers(1, max_power) == max_power);
    } else {
        if max_power * 2 <= 524288 {
            lemma_sum_increasing_bounds(n - 1, max_power * 2);
        }
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
    /* code modified by LLM (iteration 3): fixed bit shift overflow and loop logic to match spec */
    
    // Calculate start_power = 2^(l-1) using bit shift
    assert(0 <= l - 1 <= 19) by {
        assert(l >= 1);
        assert(l <= r);
        assert(r <= 20);
    }
    
    let start_power_calc: i8 = if l == 1 { 1 } else { 1i8 << ((l - 1) as u8) };
    
    proof {
        lemma_power_positive(2, (l - 1) as int);
        lemma_power_bounds((l - 1) as int);
        assert(start_power_calc as int == power(2, (l - 1) as int));
    }
    
    // Calculate minimum sum
    let mut min_sum: i8 = 0;
    let mut i: i8 = 0;
    let mut current_power: i8 = start_power_calc;
    
    while i < n
        invariant
            0 <= i <= n,
            min_sum as int == sum_with_decreasing_powers(i as int, start_power_calc as int),
            current_power as int == if i == 0 { start_power_calc as int } 
                else if start_power_calc as int / power(2, i as int) >= 1 { 
                    start_power_calc as int / power(2, i as int) 
                } else { 1 },
            current_power >= 1,
            min_sum >= 0,
            min_sum <= 127
        decreases n - i
    {
        if current_power <= 1 {
            min_sum = min_sum + 1;
        } else {
            min_sum = min_sum + current_power;
        }
        
        if current_power > 1 {
            current_power = current_power / 2;
        } else {
            current_power = 1;
        }
        i = i + 1;
    }
    
    // Calculate max_power = 2^(r-1) using bit shift
    assert(0 <= r - 1 <= 19) by {
        assert(r >= 1);
        assert(r <= 20);
    }
    
    let max_power_calc: i8 = if r == 1 { 1 } else { 1i8 << ((r - 1) as u8) };
    
    proof {
        lemma_power_positive(2, (r - 1) as int);
        lemma_power_bounds((r - 1) as int);
        assert(max_power_calc as int == power(2, (r - 1) as int));
    }
    
    // Calculate maximum sum
    let mut max_sum: i8 = max_power_calc;
    let mut j: i8 = 1;
    let mut current_max: i8 = max_power_calc;
    
    while j < n
        invariant
            1 <= j <= n,
            max_sum as int == sum_with_increasing_powers(j as int, max_power_calc as int),
            current_max as int == max_power_calc as int * power(2, (j - 1) as int),
            current_max >= 1,
            max_sum >= max_power_calc,
            max_sum <= 127
        decreases n - j
    {
        current_max = current_max * 2;
        max_sum = max_sum + current_max;
        j = j + 1;
    }
    
    proof {
        lemma_sum_decreasing_bounds(n as int, start_power_calc as int);
        lemma_sum_increasing_bounds(n as int, max_power_calc as int);
        assert(min_sum as int == min_sum_calculation(n as int, l as int));
        assert(max_sum as int == max_sum_calculation(n as int, r as int));
        assert(min_sum > 0);
        assert(max_sum > 0);
        assert(min_sum <= max_sum);
    }
    
    (min_sum, max_sum)
}
// </vc-code>


}

fn main() {}