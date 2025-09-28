// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn vec_identity(a: Vec<f32>)
    ensures
        a@ == a@,
{
}

// </vc-helpers>

// <vc-spec>
fn ravel(a: Vec<f32>) -> (result: Vec<f32>)
    ensures result@ == a@
// </vc-spec>
// <vc-code>
{
    a
}

// </vc-code>

}
fn main() {}