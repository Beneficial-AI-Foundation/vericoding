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
/* helper modified by LLM (iteration 5): lemma equating calculate_wake_time to its definition */
proof fn calculate_wake_time_equiv(a: int, b: int, c: int, d: int)
    requires
        valid_input(a, b, c, d),
    ensures
        calculate_wake_time(a, b, c, d) == {
            let remaining = a - b;
            let cycles = (remaining - 1) / (c - d) + 1;
            b + c * cycles
        },
{
    reveal(calculate_wake_time);
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
    /* code modified by LLM (iteration 5): compute wake time using machine integers and prove spec-level equality */
    let ai = a as i64;
    let bi = b as i64;
    let ci = c as i64;
    let di = d as i64;
    let mut result: i8 = 0;
    if ai <= bi {
        result = b;
    } else if ci <= di {
        result = -1;
    } else {
        let remaining = ai - bi;
        let denom = ci - di;
        let cycles = (remaining - 1) / denom + 1;
        let wake_i64 = bi + ci * cycles;
        result = #[verifier::truncate] (wake_i64 as i8);
    }

    proof {
        let ag: int = a as int;
        let bg: int = b as int;
        let cg: int = c as int;
        let dg: int = d as int;
        if ag <= bg {
            assert(result as int == bg);
        } else if cg <= dg {
            assert(result == -1);
        } else {
            reveal(calculate_wake_time);
            let remaining_g = ag - bg;
            let cycles_g = (remaining_g - 1) / (cg - dg) + 1;
            let wake_g = bg + cg * cycles_g;
            assert(result as int == wake_g);
        }
    }

    result
}

// </vc-code>


}

fn main() {}