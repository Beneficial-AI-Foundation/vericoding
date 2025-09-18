// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added complete helper functions for verification */
spec fn is_nonzero_at(a: &Vec<f64>, idx: usize) -> bool
{
    idx < a.len() && a[idx as int] != 0.0
}

spec fn indices_sorted(indices: &Vec<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] < indices[j]
}

spec fn indices_unique(indices: &Vec<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j]
}

proof fn sorted_implies_unique(indices: &Vec<usize>)
    requires indices_sorted(indices)
    ensures indices_unique(indices)
{
}
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
/* code modified by LLM (iteration 5): added decreases clause to fix compilation error */
{
    let mut indices: Vec<usize> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < indices.len() ==> 
                indices[j] < a.len() && a[indices[j] as int] != 0.0,
            forall|j: int| 0 <= j < i && a[j] != 0.0 ==> 
                indices@.contains(j as usize),
            indices_sorted(&indices),
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            indices.push(i);
        }
        i += 1;
    }
    
    proof {
        sorted_implies_unique(&indices);
    }
    
    indices
}
// </vc-code>

}
fn main() {}