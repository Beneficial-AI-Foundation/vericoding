// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed sequence indexing syntax */
fn is_sorted_and_distinct(seq: Seq<usize>) -> bool
{
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq@[i] < seq@[j]
}

fn all_nonzero_contained(a: Seq<f64>, indices: Seq<usize>, bound: int) -> bool
{
    forall|k: int| 0 <= k < bound && a@[k] != 0.0 ==> indices.contains(k as nat)
}
// </vc-helpers>

// <vc-spec>
fn numpy_argwhere(a: Vec<f64>) -> (indices: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < indices@.len() ==> 
            indices@[i] < a@.len() && a@[indices@[i] as int] != 0.0,

        forall|i: int| 0 <= i < a@.len() && a@[i] != 0.0 ==> 
            indices@.contains(i as usize),

        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> 
            indices@[i] != indices@[j],

        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> 
            indices@[i] < indices@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed sequence indexing and casting */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < indices@.len() ==> 
                indices@[k] < a@.len() && a@[indices@[k] as int] != 0.0,
            forall|k: int| 0 <= k < i && a@[k] != 0.0 ==> 
                indices@.contains(k as nat),
            forall|k: int, j: int| 0 <= k < j < indices@.len() ==> 
                indices@[k] != indices@[j],
            forall|k: int, j: int| 0 <= k < j < indices@.len() ==> 
                indices@[k] < indices@[j],
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            proof {
                assert(i < a.len());
                assert(a@[i as int] != 0.0);
                assert(forall|k: int| 0 <= k < indices@.len() ==> indices@[k] < i);
            }
            indices.push(i);
            proof {
                assert(indices@.len() > 0);
                assert(indices@[indices@.len() - 1] == i);
                assert(forall|k: int| 0 <= k < indices@.len() - 1 ==> 
                    indices@[k] < i);
            }
        }
        i += 1;
    }
    
    indices
}
// </vc-code>

}
fn main() {}