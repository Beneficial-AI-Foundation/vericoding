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
proof fn lemma_optimal_meeting_point_bounds(a: int, b: int)
    requires
        valid_input(a, b),
    ensures
        let c = optimal_meeting_point(a, b);
        c >= min(a, b),
        c <= max(a, b),
{
    /* helper modified by LLM (iteration 5): Fixed min/max function calls */
    let c = optimal_meeting_point(a, b);
    assert(a >= 1 && b >= 1);
    assert(c == (a + b) / 2);
    assert(min(a, b) <= a && min(a, b) <= b);
    assert(max(a, b) >= a && max(a, b) >= b);
}

proof fn lemma_tiredness_for_steps_formula(steps: int)
    requires
        steps >= 0,
    ensures
        tiredness_for_steps(steps) == steps * (steps + 1) / 2,
    decreases steps,
{
    if steps > 0 {
        lemma_tiredness_for_steps_formula(steps - 1);
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
{
    /* code modified by LLM (iteration 5): Fixed compilation error with min/max and proper syntax */
    let x = a as int;
    let y = b as int;
    let c_opt = (x + y) / 2;
    proof {
        lemma_optimal_meeting_point_bounds(x, y);
    }
    let dist_a = if c_opt >= x { c_opt - x } else { x - c_opt };
    let dist_b = if y >= c_opt { y - c_opt } else { c_opt - y };
    proof {
        lemma_tiredness_for_steps_formula(dist_a);
        lemma_tiredness_for_steps_formula(dist_b);
    }
    let tiredness_a = dist_a * (dist_a + 1) / 2;
    let tiredness_b = dist_b * (dist_b + 1) / 2;
    let result = tiredness_a + tiredness_b;
    assert(result >= 0);
    result as i8
}
// </vc-code>


}

fn main() {}