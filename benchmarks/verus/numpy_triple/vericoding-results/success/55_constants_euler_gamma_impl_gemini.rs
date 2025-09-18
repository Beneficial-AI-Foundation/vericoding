// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn euler_gamma() -> (result: f64)
// </vc-spec>
// <vc-code>
{
    let gamma: f64 = 0.57721566490153286060_f64;
    gamma
}
// </vc-code>

}
fn main() {}