// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    a >= 1 && a <= 1000 && b >= 1 && b <= 1000 && a != b
}

spec fn optimal_meeting_point(a: int, b: int) -> int {
    (a + b) / 2
}

spec fn tiredness_for_steps(steps: int) -> int
    decreases steps
{
    if steps <= 0 { 0 } else { steps + tiredness_for_steps(steps - 1) }
}

spec fn minimum_total_tiredness(a: int, b: int) -> int
    recommends valid_input(a, b)
{
    let c = optimal_meeting_point(a, b);
    tiredness_for_steps(if c >= a { c - a } else { a - c }) + 
    tiredness_for_steps(if b >= c { b - c } else { c - b })
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): absolute value helper */
spec fn abs_i(x: int) -> int { if x >= 0 { x } else { -x } }

/* helper modified by LLM (iteration 5): proof of tiredness formula */
proof fn tiredness_formula(steps: int)
    requires
        steps >= 0,
    ensures
        tiredness_for_steps(steps) == steps * (steps + 1) / 2,
    decreases
        steps
{
    if steps == 0 {
        assert(tiredness_for_steps(0) == 0);
        assert(0 == 0 * (0 + 1) / 2);
    } else {
        tiredness_formula(steps - 1);
        assert(tiredness_for_steps(steps) == steps + tiredness_for_steps(steps - 1));
        assert(tiredness_for_steps(steps - 1) == (steps - 1) * steps / 2);
        assert(tiredness_for_steps(steps) == steps * (steps + 1) / 2);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int),
    ensures 
        result >= 0,
        result as int == minimum_total_tiredness(a as int, b as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute meeting point and total tiredness using ghost/tracked variables and proofs */
{
    ghost let ag: int = a as int;
    ghost let bg: int = b as int;
    ghost let cg: int = optimal_meeting_point(ag, bg);
    ghost let s1: int = if cg >= ag { cg - ag } else { ag - cg };
    ghost let s2: int = if bg >= cg { bg - cg } else { cg - bg };
    proof {
        assert(s1 >= 0);
        tiredness_formula(s1);
        assert(tiredness_for_steps(s1) == s1 * (s1 + 1) / 2);
        assert(s2 >= 0);
        tiredness_formula(s2);
        assert(tiredness_for_steps(s2) == s2 * (s2 + 1) / 2);
        assert(minimum_total_tiredness(ag, bg) == tiredness_for_steps(s1) + tiredness_for_steps(s2));
    }
    tracked let total_spec: int = minimum_total_tiredness(ag, bg);
    let result: i8 = total_spec as i8;
    result
}

// </vc-code>


}

fn main() {}