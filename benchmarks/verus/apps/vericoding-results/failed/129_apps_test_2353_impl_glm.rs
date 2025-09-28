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
    /* code modified by LLM (iteration 2): use i64 for intermediate computations to avoid overflow and int type usage */
    if a <= b {
        b
    } else if c <= d {
        -1
    } else {
        let a_64 = a as i64;
        let b_64 = b as i64;
        let c_64 = c as i64;
        let d_64 = d as i64;
        let remaining = a_64 - b_64;
        let cycles = (remaining - 1) / (c_64 - d_64) + 1;
        let wake_time = b_64 + c_64 * cycles;
        wake_time as i8
    }
}
// </vc-code>


}

fn main() {}