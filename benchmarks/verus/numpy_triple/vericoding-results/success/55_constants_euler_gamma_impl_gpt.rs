// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn euler_gamma_const() -> f64 { 0.5772156649015329f64 }
// </vc-helpers>

// <vc-spec>
fn euler_gamma() -> (result: f64)
// </vc-spec>
// <vc-code>
{
    let g = euler_gamma_const();
    g
}
// </vc-code>

}
fn main() {}