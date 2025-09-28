// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [no helpers needed] */
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (result: (i32, i32))
    ensures
        result.0 == 2 * x,
        result.1 == 2 * result.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): [fix prover name from computation to compute] */
    let x_wide = x as i64;
    let d_wide = 2 * x_wide;
    let q_wide = 2 * d_wide;

    assert(i32::MIN as i64 <= d_wide <= i32::MAX as i64) by(compute);
    assert(i32::MIN as i64 <= q_wide <= i32::MAX as i64) by(compute);

    let d = d_wide as i32;
    let q = q_wide as i32;
    (d, q)
}
// </vc-code>

}
fn main() {}