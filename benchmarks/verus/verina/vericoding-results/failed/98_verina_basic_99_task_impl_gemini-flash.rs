// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed. */
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Ensured that the `assert` statements are within a `proof` block for logical reasoning and removed the invalid `indicates` keyword. */
{
    let result = x * 3;
    proof {
        assert(result / 3 == x) by(nonlinear_arith);
        assert(result / 3 * 3 == result) by(nonlinear_arith);
    }
    result
}
// </vc-code>

}
fn main() {}