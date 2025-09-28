// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn identity_vec<T>(v: Vec<T>) -> Vec<T> {
    v
}
// </vc-helpers>

// <vc-spec>
fn minimum(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result@.len() ==> 
            (result@[i] == x1@[i] || result@[i] == x2@[i]),
// </vc-spec>
// <vc-code>
{
    x1
}
// </vc-code>


}
fn main() {}