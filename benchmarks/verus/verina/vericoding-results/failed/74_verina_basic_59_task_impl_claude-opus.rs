// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (result: (i32, i32))
    ensures
        result.0 == 2 * x,
        result.1 == 2 * result.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Add overflow checks with requires clause or use wrapping arithmetic */
    let doubled = (2 as i32).wrapping_mul(x);
    let quadrupled = (2 as i32).wrapping_mul(doubled);
    (doubled, quadrupled)
}
// </vc-code>

}
fn main() {}