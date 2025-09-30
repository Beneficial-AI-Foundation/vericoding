// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn euler_gamma_const() -> f64
{
    0.5772156649015329
}
// </vc-helpers>

// <vc-spec>
fn euler_gamma() -> (result: f64)
// </vc-spec>
// <vc-code>
{
    let gamma = euler_gamma_const();
    gamma
}
// </vc-code>

}
fn main() {}