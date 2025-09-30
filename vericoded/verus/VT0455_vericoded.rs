// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermweight(x: Vec<f32>) -> (w: Vec<f32>)
    requires x.len() > 0,
    ensures
        w.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    x
}
// </vc-code>

}
fn main() {}