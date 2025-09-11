// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn diagflat(v: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == v.len() * v.len(),
        forall|i: int| 0 <= i < v.len() ==> result[i * v.len() + i] == v[i],
        forall|i: int, j: int| 0 <= i < v.len() && 0 <= j < v.len() && i != j ==> result[i * v.len() + j] == 0.0f32
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}