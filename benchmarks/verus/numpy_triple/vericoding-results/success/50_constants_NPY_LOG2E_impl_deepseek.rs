// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Remove proof function to avoid mode conflict */
fn NPY_LOG2E_internal() -> (result: f64)
    ensures result == 1.442695040888963407359924681001892137f64,
{
    1.442695040888963407359924681001892137f64
}
// </vc-helpers>

// <vc-spec>
fn NPY_LOG2E() -> (result: f64)
    ensures
        result == 1.442695040888963407359924681001892137,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Call exec function directly */
{
    NPY_LOG2E_internal()
}
// </vc-code>

}
fn main() {}