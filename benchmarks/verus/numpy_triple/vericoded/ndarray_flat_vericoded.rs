// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_index_reflexive(a: &Vec<f32>)
    ensures
        forall|i:int| 0 <= i < a.len() ==> a[i] == a[i],
{}

// </vc-helpers>

// <vc-spec>
fn numpy_flat(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
    a
}
// </vc-code>

}
fn main() {}