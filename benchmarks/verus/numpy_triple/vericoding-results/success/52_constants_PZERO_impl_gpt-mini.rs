// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn zero_f() -> f64 { 0.0 }
spec fn is_zero(x: f64) -> bool { x == 0.0 }
// </vc-helpers>

// <vc-spec>
fn pzero() -> (result: f64)
    ensures result == 0.0
// </vc-spec>
// <vc-code>
{
    0.0
}
// </vc-code>

}
fn main() {}