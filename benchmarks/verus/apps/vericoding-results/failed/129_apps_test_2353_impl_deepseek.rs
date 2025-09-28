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
proof fn lemma_calculate_wake_time_properties(
    a: int,
    b: int,
    c: int,
    d: int
)
    requires
        a > b && c > d
    ensures
        let remaining = a - b;
        let diff = c - d;
        let cycles = (remaining - 1) / diff + 1;
        cycles >= 1,
        b + c * cycles >= a
{
    let remaining = a - b;
    let diff = c - d;
    assert(remaining > 0);
    assert(diff > 0);
    
    proof {
        assert((remaining - 1) / diff + 1 >= 1);
        let cycles = (remaining - 1) / diff + 1;
        assert(diff * (cycles - 1) <= remaining - 1);
        assert(diff * (cycles - 1) + 1 <= remaining);
        assert(d * cycles + (remaining - d * (cycles - 1)) <= c * cycles);
        assert(b + d * cycles + (remaining - d * (cycles - 1)) <= b + c * cycles);
        assert(b + d * cycles + (remaining - d * (cycles - 1)) >= b + d + remaining - d);
        assert(b + d * cycles + (remaining - d * (cycles - 1)) >= b + remaining);
        assert(b + remaining == a);
    }
}

/* helper modified by LLM (iteration 5): Enhanced proof to show b + c * cycles >= a */
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
    /* code modified by LLM (iteration 5): Fixed compilation error by removing let binding */
    if a <= b {
        proof {
            lemma_first_alarm_condition(a as int, b as int);
        }
        b
    } else if c <= d {
        proof {
            lemma_never_wakes_condition(a as int, b as int, c as int, d as int);
        }
        -1
    } else {
        proof {
            lemma_eventually_wakes_condition(a as int, b as int, c as int, d as int);
            lemma_calculate_wake_time_properties(a as int, b as int, c as int, d as int);
        }
        
        let ai = a as int;
        let bi = b as int;
        let ci = c as int;
        let di = d as int;
        let remaining = ai - bi;
        let diff = ci - di;
        let cycles = (remaining - 1) / diff + 1;
        (bi + ci * cycles) as i8
    }
}
// </vc-code>


}

fn main() {}