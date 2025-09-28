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
fn sum_with_decreasing_powers_exec(n: int, start_power: int) -> int
    requires
        n >= 0,
    ensures
        result == sum_with_decreasing_powers(n, start_power),
{
    let mut i = n;
    let mut p = start_power;
    let mut acc = 0;
    while i > 0
        invariant
            i >= 0,
            acc + sum_with_decreasing_powers(i, p) == sum_with_decreasing_powers(n, start_power),
        decreases i
    {
        if p <= 1 {
            acc = acc + i;
            i = 0;
        } else {
            acc = acc + p;
            i = i - 1;
            p = p / 2;
        }
    }
    acc
}

fn sum_with_increasing_powers_exec(n: int, max_power: int) -> int
    requires
        n >= 0,
    ensures
        result == sum_with_increasing_powers(n, max_power),
{
    let mut i = n;
    let mut p = max_power;
    let mut acc = 0;
    while i > 0
        invariant
            i >= 0,
            acc + sum_with_increasing_powers(i, p) == sum_with_increasing_powers(n, max_power),
        decreases i
    {
        acc = acc + p;
        i = i - 1;
        if i > 0 {
            p = p * 2;
        }
    }
    acc
}

fn min_sum_int(n: int, l: int) -> int
    requires
        n >= 1,
        l >= 1,
    ensures
        result == min_sum_calculation(n, l),
{
    let start_power = power(2, l - 1);
    sum_with_decreasing_powers_exec(n, start_power)
}

fn max_sum_int(n: int, r: int) -> int
    requires
        n >= 1,
        r >= 1,
    ensures
        result == max_sum_calculation(n, r),
{
    let max_power = power(2, r - 1);
    sum_with_increasing_powers_exec(n, max_power)
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
    let ni: int = n as int;
    let li: int = l as int;
    let ri: int = r as int;

    let min_i: int = min_sum_int(ni, li);
    let max_i: int = max_sum_int(ni, ri);

    let min_res: i8 = min_i as i8;
    let max_res: i8 = max_i as i8;

    (min_res, max_res)
}
// </vc-code>


}

fn main() {}