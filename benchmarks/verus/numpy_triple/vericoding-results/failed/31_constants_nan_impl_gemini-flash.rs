// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed code that caused compilation errors with f64::NAN */
spec fn nan_helper() -> f64 { 0.0 / 0.0 }
// </vc-helpers>

// <vc-spec>
fn nan() -> (result: f64)
    ensures result != result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Updated to use the corrected `nan_helper` and assert the postcondition. */
{
    let result = nan_helper();
    assert(result != result);
    result
}
// </vc-code>

}
fn main() {}