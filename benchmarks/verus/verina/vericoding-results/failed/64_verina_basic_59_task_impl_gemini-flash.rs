// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers section for this problem */
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (result: (i32, i32))
    ensures
        result.0 == 2 * x,
        result.1 == 2 * result.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed extraneous `requires` call within function body. */
    let doubled: i32 = 2 * x;
    let quadrupled: i32 = 2 * doubled;
    (doubled, quadrupled)
}
// </vc-code>

}
fn main() {}