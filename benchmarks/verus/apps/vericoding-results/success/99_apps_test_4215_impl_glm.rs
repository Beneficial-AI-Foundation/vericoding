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
    /* code modified by LLM (iteration 2): avoid overflow by handling large b values separately */
    if b >= 64 {
        0
    } else {
        let two_b = b + b;
        if a > two_b {
            a - two_b
        } else {
            0
        }
    }
}
// </vc-code>


}

fn main() {}