// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use f64::NAN constant */
fn get_nan() -> (result: f64)
    ensures result != result
{
    f64::NAN
}
// </vc-helpers>

// <vc-spec>
fn nan() -> (result: f64)
    ensures result != result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): call helper to get NaN */
{
    get_nan()
}
// </vc-code>

}
fn main() {}