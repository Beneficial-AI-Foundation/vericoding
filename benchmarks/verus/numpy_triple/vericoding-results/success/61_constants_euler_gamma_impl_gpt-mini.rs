// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn approx_euler() -> f64 {
    0.5772156649015328606_f64
}
// </vc-helpers>

// <vc-spec>
fn euler_gamma() -> (result: f64)
// </vc-spec>
// <vc-code>
{
    let result: f64 = approx_euler();
    result
}
// </vc-code>

}
fn main() {}