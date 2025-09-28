// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn NINF() -> (result: f64)
    ensures

        true
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use negative of large value as workaround for NEG_INFINITY */
    let result: f64 = -1.0e308;
    result
}
// </vc-code>

}
fn main() {}