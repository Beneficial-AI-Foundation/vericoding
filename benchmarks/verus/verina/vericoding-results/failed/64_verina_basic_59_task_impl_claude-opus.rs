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
    /* code modified by LLM (iteration 5): Add overflow checks for i32 arithmetic */
    if x < i32::MIN / 2 || x > i32::MAX / 2 {
        // Cannot compute 2*x without overflow
        return (0, 0);
    }
    let doubled = 2 * x;
    if doubled < i32::MIN / 2 || doubled > i32::MAX / 2 {
        // Cannot compute 2*doubled without overflow
        return (0, 0);
    }
    let quadrupled = 2 * doubled;
    (doubled, quadrupled)
}
// </vc-code>

}
fn main() {}