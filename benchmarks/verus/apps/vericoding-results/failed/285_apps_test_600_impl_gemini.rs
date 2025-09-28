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
/* helper modified by LLM (iteration 2): completed inductive proof skeleton */
proof fn lemma_tiredness_is_arithmetic_sum(steps: int)
    requires
        steps >= 0,
    ensures
        tiredness_for_steps(steps) == steps * (steps + 1) / 2,
    decreases steps,
{
    if steps > 0 {
        lemma_tiredness_is_arithmetic_sum(steps - 1);
        assert(tiredness_for_steps(steps) == steps + tiredness_for_steps(steps - 1));
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
    /* code modified by LLM (iteration 2): fixed compilation error by using exec types for computation */
    let a_exec = a as i32;
    let b_exec = b as i32;

    let c_exec = (a_exec + b_exec) / 2;

    let steps_a_exec = if c_exec >= a_exec { c_exec - a_exec } else { a_exec - c_exec };
    let steps_b_exec = if c_exec >= b_exec { c_exec - b_exec } else { b_exec - c_exec };

    let tiredness_a_exec = steps_a_exec * (steps_a_exec + 1) / 2;
    let tiredness_b_exec = steps_b_exec * (steps_b_exec + 1) / 2;

    let total_tiredness_exec = tiredness_a_exec + tiredness_b_exec;

    proof {
        let a_spec = a as int;
        let b_spec = b as int;
        let c_spec = optimal_meeting_point(a_spec, b_spec);
        let steps_a_spec = if c_spec >= a_spec { c_spec - a_spec } else { a_spec - c_spec };
        let steps_b_spec = if b_spec >= c_spec { b_spec - c_spec } else { c_spec - b_spec };

        assert(steps_a_exec as int == steps_a_spec) by {
            assert(a_exec as int == a_spec);
            assert(b_exec as int == b_spec);
            assert(c_exec as int == c_spec);
        };
        assert(steps_b_exec as int == steps_b_spec) by {
            assert(a_exec as int == a_spec);
            assert(b_exec as int == b_spec);
            assert(c_exec as int == c_spec);
        };

        lemma_tiredness_is_arithmetic_sum(steps_a_spec);
        lemma_tiredness_is_arithmetic_sum(steps_b_spec);

        assert(tiredness_a_exec as int == tiredness_for_steps(steps_a_spec));
        assert(tiredness_b_exec as int == tiredness_for_steps(steps_b_spec));

        assert(total_tiredness_exec as int == minimum_total_tiredness(a_spec, b_spec));
    }

    total_tiredness_exec as i8
}

// </vc-code>


}

fn main() {}