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
/* helper modified by LLM (iteration 3): calc_sum_decreasing wrapper */
spec fn calc_sum_decreasing(n: int, start_power: int) -> int {
    sum_with_decreasing_powers(n, start_power)
}

/* helper modified by LLM (iteration 3): calc_sum_increasing wrapper */
spec fn calc_sum_increasing(n: int, max_power: int) -> int {
    sum_with_increasing_powers(n, max_power)
}

/* helper modified by LLM (iteration 3): calc_min_sum wrapper */
spec fn calc_min_sum(n: int, l: int) -> int {
    if n >= 1 && l >= 1 {
        let start_power = power(2, l - 1);
        calc_sum_decreasing(n, start_power)
    } else {
        0
    }
}

/* helper modified by LLM (iteration 3): calc_max_sum wrapper */
spec fn calc_max_sum(n: int, r: int) -> int {
    if n >= 1 && r >= 1 {
        let max_power = power(2, r - 1);
        calc_sum_increasing(n, max_power)
    } else {
        0
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
    /* code modified by LLM (iteration 3): compute min/max sums at runtime and prove equivalence to spec */
    let mut rem: i64 = n as i64;
    let mut sp: i64 = 1i64 << ((l as i64) - 1);
    let mut min_sum: i64 = 0i64;
    while rem > 0 && sp > 1
        invariant
            rem as int >= 0,
        decreases rem as int
    {
        min_sum += sp;
        rem -= 1;
        sp /= 2;
    }
    if rem > 0 {
        min_sum += rem;
        rem = 0;
    }

    let mut rem2: i64 = n as i64;
    let mut mp: i64 = 1i64 << ((r as i64) - 1);
    let mut max_sum: i64 = 0i64;
    while rem2 > 0
        invariant
            rem2 as int >= 0,
        decreases rem2 as int
    {
        max_sum += mp;
        rem2 -= 1;
        mp *= 2;
    }

    let min_i8: i8 = min_sum as i8;
    let max_i8: i8 = max_sum as i8;

    proof {
        let n_ghost: int = n as int;
        let l_ghost: int = l as int;
        let r_ghost: int = r as int;
        let min_ghost: int = min_sum as int;
        let max_ghost: int = max_sum as int;

        assert(min_ghost == calc_min_sum(n_ghost, l_ghost));
        assert(max_ghost == calc_max_sum(n_ghost, r_ghost));
        assert(min_ghost > 0);
        assert(max_ghost > 0);
        assert(min_ghost as i8 == min_i8);
        assert(max_ghost as i8 == max_i8);
    }

    (min_i8, max_i8)
}

// </vc-code>


}

fn main() {}