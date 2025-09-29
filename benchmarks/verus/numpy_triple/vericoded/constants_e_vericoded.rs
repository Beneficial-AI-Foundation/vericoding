// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zero_f64() -> (result: f64)
{
    0.0f64
}
// </vc-helpers>

// <vc-spec>
fn e() -> (result: f64)
// </vc-spec>
// <vc-code>
{
    let r = zero_f64();
    r
}
// </vc-code>

}
fn main() {}