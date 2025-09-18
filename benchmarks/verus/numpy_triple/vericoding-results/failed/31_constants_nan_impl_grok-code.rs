// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nan() -> (result: f64)
    ensures result != result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): relying on f64::NAN to satisfy result != result ensures */
    f64::NAN
}
// </vc-code>

}
fn main() {}