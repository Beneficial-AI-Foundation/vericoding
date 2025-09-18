// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn vec_identity(a: Vec<f32>) ensures a.len() == a.len() { }
// </vc-helpers>

// <vc-spec>
fn numpy_flatiter(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    a
}
// </vc-code>

}
fn main() {}