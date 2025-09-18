// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected helper body; Verus can prove NaN inequality from axioms. */
proof fn lemma_my_nan_not_equal(f: f64)
    requires
        f.is_nan(),
    ensures
        f != f,
{
}
// </vc-helpers>

// <vc-spec>
fn nan() -> (result: f64)
    ensures result != result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Replaced non-existent function with f64::NAN constant. */
    let result = f64::NAN;
    proof {
        lemma_my_nan_not_equal(result);
    }
    result
}
// </vc-code>

}
fn main() {}