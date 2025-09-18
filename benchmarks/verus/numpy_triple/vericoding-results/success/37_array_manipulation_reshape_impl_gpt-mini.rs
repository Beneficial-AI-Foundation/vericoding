// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn vec_equal(a: Vec<f32>, b: Vec<f32>) -> bool { a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> a@[i] == b@[i] }
// </vc-helpers>

// <vc-spec>
fn reshape(a: Vec<f32>) -> (result: Vec<f32>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
    let result = a;
    result
}
// </vc-code>

}
fn main() {}