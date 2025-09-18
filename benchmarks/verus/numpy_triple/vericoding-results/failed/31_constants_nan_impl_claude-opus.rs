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
    /* code modified by LLM (iteration 5): create NaN by dividing 0.0 by 0.0 */
    let zero: f64 = 0.0;
    let result: f64 = zero / zero;
    result
}
// </vc-code>

}
fn main() {}