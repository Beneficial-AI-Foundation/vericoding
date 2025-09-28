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
/* code modified by LLM (iteration 3): Add missing opening and closing braces around the function body. */
    let a64 = a as i64;
    let b64 = b as i64;
    let diff = if a64 > 2 * b64 { a64 - 2 * b64 } else { 0 };
    diff as i8
}
// </vc-code>


}

fn main() {}