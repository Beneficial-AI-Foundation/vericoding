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
/* helper modified by LLM (iteration 2): changed types from nat to u32 for executable code */
fn exec_tiredness(steps: u32) -> u32
    decreases steps
{
    if steps == 0 { 0 } else { steps + exec_tiredness(steps - 1) }
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
/* code modified by LLM (iteration 2): changed types to use i32 for int and u32 for nat in executable code */
{
    let c: i32 = (a as i32 + b as i32) / 2;
    let steps_a: i32 = if c >= a as i32 { c - a as i32 } else { a as i32 - c };
    let steps_b: i32 = if b as i32 >= c { b as i32 - c } else { c - b as i32 };
    let ta = exec_tiredness(steps_a as u32);
    let tb = exec_tiredness(steps_b as u32);
    let total = ta as i32 + tb as i32;
    total as i8
}
// </vc-code>


}

fn main() {}