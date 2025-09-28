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
    /* code modified by LLM (iteration 3): use wrapping multiplication to avoid panic */
    let double = x.wrapping_mul(2);
    let quadruple = double.wrapping_mul(2);
    (double, quadruple)
}
// </vc-code>

}
fn main() {}