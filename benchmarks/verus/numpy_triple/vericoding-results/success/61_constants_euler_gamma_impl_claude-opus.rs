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
    let gamma: f64 = 0.5772156649015329;
    gamma
}
// </vc-code>

}
fn main() {}