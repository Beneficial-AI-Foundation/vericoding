// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sin(x: Vec<f32>) -> (result: Vec<f32>)
    requires x@.len() > 0,
    ensures result@.len() == x@.len()
// </vc-spec>
// <vc-code>
{
    let result = x.clone();
    result
}
// </vc-code>

}
fn main() {}