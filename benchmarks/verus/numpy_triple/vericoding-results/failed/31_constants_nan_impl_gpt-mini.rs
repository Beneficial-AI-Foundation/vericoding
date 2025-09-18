// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide is_nan predicate */
spec fn is_nan(x: f64) -> bool { x != x }
// </vc-helpers>

// <vc-spec>
fn nan() -> (result: f64)
    ensures result != result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct NaN via f64::from_bits and prove it's NaN */
    let result: f64 = f64::from_bits(0x7ff8000000000001u64);
    proof {
        assert(result != result);
    }
    result
}
// </vc-code>

}
fn main() {}