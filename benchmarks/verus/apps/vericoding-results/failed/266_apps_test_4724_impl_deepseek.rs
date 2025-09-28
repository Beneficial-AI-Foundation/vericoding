// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(r: int, g: int) -> bool {
    0 <= r <= 4500 && 0 <= g <= 4500
}

spec fn required_performance(r: int, g: int) -> int {
    2 * g - r
}

spec fn correct_result(r: int, g: int, p: int) -> bool {
    (r + p) == 2 * g
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_arithmetic_identity(r: int, g: int)
    requires
        valid_input(r, g)
    ensures
        correct_result(r, g, required_performance(r, g))
{
    assert(r + (2 * g - r) == 2 * g);
}
// </vc-helpers>

// <vc-spec>
fn solve(r: i8, g: i8) -> (result: i8)
    requires 
        valid_input(r as int, g as int)
    ensures 
        result as int == required_performance(r as int, g as int) &&
        correct_result(r as int, g as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Add bounds checking to prevent overflow */
    assert((2 * g as int) - r as int >= -128 && (2 * g as int) - r as int <= 127);
    let p: i8 = ((2 * g) - r) as i8;
    proof {
        lemma_arithmetic_identity(r as int, g as int);
    }
    p
}
// </vc-code>


}

fn main() {}