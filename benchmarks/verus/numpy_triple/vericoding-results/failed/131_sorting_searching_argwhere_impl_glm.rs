// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_strictly_increasing(s: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}
/* helper modified by LLM (iteration 5): no changes needed */
// </vc-helpers>

// <vc-spec>
fn numpy_argwhere(a: Vec<f64>) -> (indices: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < indices.len() ==> 
            indices[i] < a.len() && a[indices[i] as int] != 0.0,

        forall|i: int| 0 <= i < a.len() && a[i] != 0.0 ==> 
            indices@.contains(i as usize),

        forall|i: int, j: int| 0 <= i < j < indices.len() ==> 
            indices[i] != indices[j],

        forall|i: int, j: int| 0 <= i < j < indices.len() ==> 
            indices[i] < indices[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariants to maintain proper inductive properties */
    let mut indices: Vec<usize> = Vec::new();
    for i in 0..a.len()
        invariant
            forall|k: int| 0 <= k < indices.len() ==> indices[k] < a.len(),
            forall|k: int| 0 <= k < indices.len() ==> 
                #[trigger] a[indices[k] as int] != 0.0,
            forall|k: int| 0 <= k < (i as int) && #[trigger] a[k] != 0.0 ==> 
                indices@.contains(k as usize),
            is_strictly_increasing(indices@),
    {
        proof {
            if a[i] != 0.0 {
                assert(indices@.contains(i as usize));
            }
        }
        if a[i] != 0.0 {
            indices.push(i);
        }
    }
    indices
}
// </vc-code>

}
fn main() {}