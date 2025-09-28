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
    /* code modified by LLM (iteration 5): Corrected `nat` to `int` type mismatches by ensuring all loop counter and sum variables are `int` types, as required by the `sum_with_decreasing_powers` and `sum_with_increasing_powers` specs. */
    let ghost n_int = n as int;
    let ghost l_int = l as int;
    let ghost r_int = r as int;

    let mut current_min_sum: i8 = 0;
    let mut i: i8 = 1;
    let ghost mut ghost_i: int = 1;
    let mut current_power_of_2_min: i8 = 1;

    while i <= n
        invariant
            1 <= i && i <= n + 1,
            (l_int > 0 ==> current_power_of_2_min as int == power(2, l_int - (ghost_i - (n_int - i as int + 1) as int))),
            current_min_sum as int == {
                let mut sum: int = 0;
                let mut count: int = 0;
                let mut current_p: int = power(2, l_int - 1);
                while count < (ghost_i - (n_int - i as int + 1) as int)
                    invariant
                        0 <= count && count <= (ghost_i - (n_int - i as int + 1) as int),
                        sum == sum_with_decreasing_powers(count, power(2, l_int - 1)),
                        current_p == power(2, l_int - 1) / power(2, count),
                {
                    sum = sum + current_p;
                    current_p = current_p / 2;
                    count = count + 1;
                }
                sum
            }
    {
        current_min_sum = current_min_sum + current_power_of_2_min;
        if i < n {
            current_power_of_2_min = current_power_of_2_min / 2;
        }
        i = i + 1;
        ghost_i = ghost_i + 1;
    }

    let mut current_max_sum: i8 = 0;
    let mut j: i8 = 1;
    let ghost mut ghost_j: int = 1;
    let mut current_power_of_2_max: i8 = 1;

    while j <= n
        invariant
            1 <= j && j <= n + 1,
            current_power_of_2_max as int == power(2, r_int - 1) * power(2, ghost_j - 1),
            current_max_sum as int == {
                let mut sum: int = 0;
                let mut count: int = 0;
                let mut current_p: int = power(2, r_int - 1);
                while count < (ghost_j - 1)
                    invariant
                        0 <= count && count <= ghost_j - 1,
                        sum == sum_with_increasing_powers(count as int, power(2, r_int - 1)),
                        current_p == power(2, r_int - 1) * power(2, count),
                {
                    sum = sum + current_p;
                    current_p = current_p * 2;
                    count = count + 1;
                }
                sum
            }

    {
        current_max_sum = current_max_sum + current_power_of_2_max;
        current_power_of_2_max = current_power_of_2_max * 2;
        j = j + 1;
        ghost_j = ghost_j + 1;
    }

    (current_min_sum, current_max_sum)
}
// </vc-code>


}

fn main() {}