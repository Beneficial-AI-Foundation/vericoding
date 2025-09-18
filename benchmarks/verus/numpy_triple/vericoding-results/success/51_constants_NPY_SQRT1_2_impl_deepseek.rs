// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Renamed helper function to avoid name collision */
fn npy_sqrt1_2_helper() -> (result: f64) {
    let sqrt_half: f64 = 0.7071067811865476;
    sqrt_half
}
// </vc-helpers>

// <vc-spec>
fn NPY_SQRT1_2() -> (result: f64)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Call helper function to avoid duplicate definition */
{
    npy_sqrt1_2_helper()
}
// </vc-code>

}
fn main() {}