// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): defined a helper to obtain NEG_INFINITY via external_body */
#[verifier(external_body)]
fn get_neg_inf() -> (result: f64)
    ensures
        true,
{
    core::f64::NEG_INFINITY
}
// </vc-helpers>

// <vc-spec>
fn NINF() -> (result: f64)
    ensures

        true
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): called helper to get NEG_INFINITY */
    get_neg_inf()
}
// </vc-code>

}
fn main() {}