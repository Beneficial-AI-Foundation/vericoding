// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove problematic div_f64 spec function and use built-in division */
spec fn is_nan(x: f64) -> bool { !(x == x) }
proof fn nan_division_lemma() ensures is_nan(0f64 / 0f64) {
    assert((0f64 / 0f64) != (0f64 / 0f64));
}
// </vc-helpers>

// <vc-spec>
fn nan() -> (result: f64)
    ensures result != result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use direct floating point division */
{
    0f64 / 0f64
}
// </vc-code>

}
fn main() {}