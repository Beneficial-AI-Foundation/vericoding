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
/* helper modified by LLM (iteration 5): fix integer literal type mismatches by using int literals */
fn lemma_tiredness_steps_nonneg(steps: int)
    ensures tiredness_for_steps(steps) >= 0
    decreases steps
{
    if steps <= 0int {
    } else {
        lemma_tiredness_steps_nonneg(steps - 1int);
    }
}

fn lemma_tiredness_formula(steps: int)
    requires steps >= 0
    ensures tiredness_for_steps(steps) == steps * (steps + 1int) / 2int
    decreases steps
{
    if steps == 0int {
    } else {
        lemma_tiredness_formula(steps - 1int);
    }
}

fn lemma_abs_diff(x: int, y: int)
    ensures (if x >= y { x - y } else { y - x }) >= 0
{
}

fn lemma_meeting_point_optimal(a: int, b: int)
    requires valid_input(a, b)
    ensures
        optimal_meeting_point(a, b) >= 1int && optimal_meeting_point(a, b) <= 1000int
{
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
    /* code modified by LLM (iteration 5): fix integer literal type mismatches and implement proper calculation */
    let c = (a + b) / 2;
    
    let steps_a = if c >= a { c - a } else { a - c };
    let steps_b = if b >= c { b - c } else { c - b };
    
    proof {
        lemma_abs_diff(a as int, c as int);
        lemma_abs_diff(b as int, c as int);
        lemma_tiredness_steps_nonneg(steps_a as int);
        lemma_tiredness_steps_nonneg(steps_b as int);
        lemma_tiredness_formula(steps_a as int);
        lemma_tiredness_formula(steps_b as int);
        lemma_meeting_point_optimal(a as int, b as int);
        
        assert(c as int == optimal_meeting_point(a as int, b as int));
        assert(steps_a as int == (if c as int >= a as int { c as int - a as int } else { a as int - c as int }));
        assert(steps_b as int == (if b as int >= c as int { b as int - c as int } else { c as int - b as int }));
    }
    
    let tiredness_a = steps_a * (steps_a + 1) / 2;
    let tiredness_b = steps_b * (steps_b + 1) / 2;
    
    tiredness_a + tiredness_b
}
// </vc-code>


}

fn main() {}