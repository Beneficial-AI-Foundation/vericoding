// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn npy_loge2() -> (result: f64)
    ensures
        result == 0.693147180559945309417232121458176568
// </vc-spec>
// <vc-code>
{
    let result: f64 = 0.693147180559945309417232121458176568;
    result
}
// </vc-code>


}
fn main() {}