// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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