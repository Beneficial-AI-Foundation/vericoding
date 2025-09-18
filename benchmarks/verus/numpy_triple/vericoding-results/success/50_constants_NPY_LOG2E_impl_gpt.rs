// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn npy_log2e_const() -> (result: f64)
    ensures
        result == 1.442695040888963407359924681001892137,
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
{
    let c = npy_log2e_const();
    c
}
// </vc-code>

}
fn main() {}