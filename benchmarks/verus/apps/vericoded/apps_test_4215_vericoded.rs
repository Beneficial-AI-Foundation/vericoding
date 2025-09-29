// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100
}

spec fn uncovered_length(a: int, b: int) -> int {
    if a - 2 * b > 0 { a - 2 * b } else { 0 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int)
    ensures 
        result >= 0,
        result as int == uncovered_length(a as int, b as int),
        result as int == if a as int > 2 * (b as int) { a as int - 2 * (b as int) } else { 0 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [fixed compilation errors by using a concrete integer type (i32) for arithmetic to avoid overflow and invalid type usage] */
    let a_wide = a as i32;
    let b_wide = b as i32;
    if a_wide > 2 * b_wide {
        (a_wide - 2 * b_wide) as i8
    } else {
        0
    }
}
// </vc-code>


}

fn main() {}