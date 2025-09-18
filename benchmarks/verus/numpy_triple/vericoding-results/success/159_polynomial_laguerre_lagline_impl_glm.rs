// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lagline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures result.len() == 2
// </vc-spec>
// <vc-code>
{
    vec![off, scl]
}
// </vc-code>

}
fn main() {}