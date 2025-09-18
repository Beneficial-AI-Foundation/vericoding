// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): wrapped the unsupported f32::INFINITY constant in an external_body function to allow compilation */
#[verifier(external_body)]
fn get_infinity() -> f32 {
    f32::INFINITY
}
// </vc-helpers>

// <vc-spec>
fn inf() -> (result: f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): called the external_body helper to obtain the f32::INFINITY value */
    get_infinity()
}
// </vc-code>

}
fn main() {}