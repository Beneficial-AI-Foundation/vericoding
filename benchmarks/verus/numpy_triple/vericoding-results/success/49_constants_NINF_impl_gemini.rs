// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): defined external_body function to produce NEG_INFINITY */
#[verifier(external_body)]
fn get_neg_infinity() -> (r: f64)
    ensures true,
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
/* code modified by LLM (iteration 2): called helper to return NEG_INFINITY */
{
    get_neg_infinity()
}
// </vc-code>

}
fn main() {}