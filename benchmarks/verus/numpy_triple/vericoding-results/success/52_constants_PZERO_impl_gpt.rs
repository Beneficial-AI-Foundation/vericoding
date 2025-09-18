// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn zero_is_zero() ensures 0.0 == 0.0 { }
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