// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn log2e_val()
    ensures
        1.442695040888963407359924681001892137f64 == 1.4426950408889634f64,
{
    // Direct equality proof for the constant value
    assert(1.442695040888963407359924681001892137f64 == 1.4426950408889634f64);
}
// </vc-helpers>

// <vc-spec>
fn NPY_LOG2E() -> (result: f64)
    ensures
        result == 1.442695040888963407359924681001892137,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Return exact constant value */
    1.442695040888963407359924681001892137f64
}
// </vc-code>

}
fn main() {}