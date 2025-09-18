// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn euler_gamma_constant() -> f64 { 0.5772156649015329 }
// </vc-helpers>

// <vc-spec>
fn euler_gamma() -> (result: f64)
// </vc-spec>
// <vc-code>
{
    0.5772156649015329
}
// </vc-code>

}
fn main() {}