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
    let result: f64 = 0.57721566490153286060651209008240243104215933593992;
    result
}
// </vc-code>

}
fn main() {}