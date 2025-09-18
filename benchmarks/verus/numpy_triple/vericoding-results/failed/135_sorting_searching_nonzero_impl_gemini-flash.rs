// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nonzero(a: Vec<f32>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices.len() ==> (indices[i] < a.len() && a[indices[i] as int] != 0.0f32),
        forall|j: int| 0 <= j < a.len() ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j),
        forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed invariants to satisfy the end of the loop body for verification. */
{
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant 
            0 <= i as int && i as int <= a.len(),
            forall|k: int| 0 <= k < indices.len() ==> (indices[k] < a.len() && a[indices[k] as int] != 0.0f32),
            forall|j: int| 0 <= j < i as int ==> (a[j as int] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j as usize),
            forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
            
        decreases a.len() - i
    {
        if a[i] != 0.0f32 {
            indices.push(i);
            proof {
                //@ assert(indices.last().is_Some());
                //@ assert(indices.last().unwrap() == i as usize);
            }
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}