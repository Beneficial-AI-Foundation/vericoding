// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

fn ravel_proof(a: Vec<f32>) -> (result: Vec<f32>)
    ensures result@ == a@
{
    a
}

// </vc-helpers>

// <vc-spec>
fn ravel(a: Vec<f32>) -> (result: Vec<f32>)
    ensures result@ == a@
// </vc-spec>
// <vc-code>
{
    ravel_proof(a)
}
// </vc-code>

}
fn main() {}