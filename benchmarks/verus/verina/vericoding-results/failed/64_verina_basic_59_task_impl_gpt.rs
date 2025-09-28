// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial helper retained; no additional proof needed */
proof fn helper_trivial() { }
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (result: (i32, i32))
    ensures
        result.0 == 2 * x,
        result.1 == 2 * result.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute using direct multiplication to align with ensures */
    let d: i32 = 2 * x;
    let q: i32 = 2 * d;
    (d, q)
}
// </vc-code>

}
fn main() {}