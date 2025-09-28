// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn ln2_const() -> (result: f64)
    ensures
        result == 0.693147180559945309417232121458176568
{
    0.693147180559945309417232121458176568
}
// </vc-helpers>

// <vc-spec>
fn npy_loge2() -> (result: f64)
    ensures
        result == 0.693147180559945309417232121458176568
// </vc-spec>
// <vc-code>
{
    0.693147180559945309417232121458176568
}
// </vc-code>


}
fn main() {}