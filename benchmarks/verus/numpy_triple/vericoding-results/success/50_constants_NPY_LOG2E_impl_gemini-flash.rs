// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
const NPY_LOG2E_VALUE: f64 = 1.442695040888963407359924681001892137;

// </vc-helpers>

// <vc-spec>
fn NPY_LOG2E() -> (result: f64)
    ensures
        result == 1.442695040888963407359924681001892137,
// </vc-spec>
// <vc-code>
{
    NPY_LOG2E_VALUE
}
// </vc-code>

}
fn main() {}