// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn helper_log2e() -> (result: f64)
    ensures
        result == 1.442695040888963407359924681001892137,
{
    let r: f64 = 1.442695040888963407359924681001892137_f64;
    r
}
// </vc-helpers>

// <vc-spec>
fn NPY_LOG2E() -> (result: f64)
    ensures
        result == 1.442695040888963407359924681001892137,
// </vc-spec>
// <vc-code>
{
    helper_log2e()
}
// </vc-code>

}
fn main() {}