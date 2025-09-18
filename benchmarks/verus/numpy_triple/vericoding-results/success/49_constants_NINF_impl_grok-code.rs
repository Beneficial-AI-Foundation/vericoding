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
    /* code modified by LLM (iteration 4): Return a large negative float to approximate -infinity, avoiding unsupported f64::NEG_INFINITY */
    -1e308
}
// </vc-code>

}
fn main() {}