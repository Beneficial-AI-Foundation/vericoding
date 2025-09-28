// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    a >= 0 && b >= 0 && c >= 0 && d >= 0
}

spec fn first_alarm_sufficient(a: int, b: int) -> bool {
    a <= b
}

spec fn never_wakes(a: int, b: int, c: int, d: int) -> bool {
    a > b && c <= d
}

spec fn eventually_wakes(a: int, b: int, c: int, d: int) -> bool {
    a > b && c > d
}

spec fn calculate_wake_time(a: int, b: int, c: int, d: int) -> int {
    let remaining = a - b;
    let cycles = (remaining - 1) / (c - d) + 1;
    b + c * cycles
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): bounds for ceil-div and link to spec calculation */
spec fn ceil_div_pos(n: int, d: int) -> int {
    if n <= 0 { 0 } else { (n - 1) / d + 1 }
}

proof fn lemma_ceil_div_bounds(n: int, d: int)
    requires
        n >= 0,
        d >= 1,
    ensures
        0 <= ceil_div_pos(n, d),
        ceil_div_pos(n, d) <= n,
{
    if n == 0 {
        assert(ceil_div_pos(n, d) == 0);
    } else {
        assert(ceil_div_pos(n, d) == (n - 1) / d + 1);
        assert((n - 1) / d <= n - 1);
        assert(ceil_div_pos(n, d) <= (n - 1) + 1);
        assert(ceil_div_pos(n, d) <= n);
    }
}

proof fn lemma_calc_eq(a: int, b: int, c: int, d: int)
    requires
        valid_input(a, b, c, d),
        a > b,
        c > d,
    ensures
        calculate_wake_time(a, b, c, d) == b + c * ceil_div_pos(a - b, c - d),
{
    assert(a - b > 0);
    assert(c - d > 0);
    assert(ceil_div_pos(a - b, c - d) == (a - b - 1) / (c - d) + 1);
    assert(calculate_wake_time(a, b, c, d) == {
        let remaining = a - b;
        let cycles = (remaining - 1) / (c - d) + 1;
        b + c * cycles
    });
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int, d as int)
    ensures 
        first_alarm_sufficient(a as int, b as int) ==> result as int == b as int,
        never_wakes(a as int, b as int, c as int, d as int) ==> result == -1,
        eventually_wakes(a as int, b as int, c as int, d as int) ==> result as int == calculate_wake_time(a as int, b as int, c as int, d as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute wake time safely in i32 and add bounds assertions to avoid overflow */
    if a <= b {
        b
    } else if c <= d {
        -1
    } else {
        let remaining: i32 = (a as i32) - (b as i32);
        let diff: i32 = (c as i32) - (d as i32);
        proof {
            assert(0 <= a as i32 && a as i32 <= 127);
            assert(0 <= b as i32 && b as i32 <= 127);
            assert(0 <= c as i32 && c as i32 <= 127);
            assert(0 <= d as i32 && d as i32 <= 127);
            assert(remaining >= 1);
            assert(remaining <= 127);
            assert(diff >= 1);
            assert(diff <= 127);
        }
        let cycles: i32 = ((remaining - 1) / diff) + 1;
        proof {
            assert(((remaining - 1) / diff) + 1 <= remaining);
            assert(((remaining - 1) / diff) + 1 >= 0);
            assert(cycles <= remaining);
            assert(cycles >= 0);
            assert(cycles <= 127);
            assert((c as i32) * cycles >= 0);
            assert((c as i32) * cycles <= 127 * 127);
            assert((b as i32) + (c as i32) * cycles <= 127 + 127 * 127);
            assert((b as i32) + (c as i32) * cycles <= 2147483647);
        }
        let wake: i32 = (b as i32) + (c as i32) * cycles;
        wake as i8
    }
}
// </vc-code>


}

fn main() {}