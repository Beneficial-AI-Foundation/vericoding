// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn pzero_helper() -> (result: f64) ensures result == 0.0 { 0.0 }
// </vc-helpers>

// <vc-spec>
fn pzero() -> (result: f64)
    ensures result == 0.0
// </vc-spec>
// <vc-code>
{
    pzero_helper()
}
// </vc-code>

}
fn main() {}