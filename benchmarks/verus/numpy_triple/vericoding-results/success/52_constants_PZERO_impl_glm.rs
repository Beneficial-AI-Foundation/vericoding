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
    let result = 0.0;
    result
}
// </vc-code>

}
fn main() {}