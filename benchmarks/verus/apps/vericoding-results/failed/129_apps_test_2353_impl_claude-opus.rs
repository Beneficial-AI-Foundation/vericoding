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
    /* code modified by LLM (iteration 5): Fixed compilation errors by using i8 arithmetic instead of int conversions */
    if a <= b {
        b
    } else if c <= d {
        -1
    } else {
        // Calculate cycles needed using i8 arithmetic
        let mut cycles: i8 = 0;
        let mut total_sleep: i8 = b;
        
        while total_sleep < a
            invariant
                cycles >= 0,
                total_sleep as int == b as int + (c as int - d as int) * cycles as int,
                total_sleep >= b,
                total_sleep as int <= 127,
            decreases (a as int - total_sleep as int) as nat
        {
            cycles = cycles + 1;
            total_sleep = total_sleep + c - d;
        }
        
        b + c * cycles
    }
}
// </vc-code>


}

fn main() {}