// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed */
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
/* code modified by LLM (iteration 5): Fixed type errors by adding as int casts in invariants for consistency */
{
    let mut i: usize = 0;
    let mut indices: Vec<usize> = Vec::new();
    while i < a.len()
        invariant
            i as int <= a@.len(),
            a@.len() == a.len() as int,
            indices@.len() <= i as int,
            forall|j: int| 0 <= j < indices@.len() ==> 
                (indices@[j] as int) < a@.len() && a@[indices@[j] as int] != 0.0 && (indices@[j] as int) <= i as int,
            forall|k: int| 0 <= k < i as int && a@[k] != 0.0 ==> 
                indices@.contains(k as usize),
            forall|j: int, r: int| 0 <= j < r < indices@.len() ==> 
                (indices@[j] as int) < (indices@[r] as int),
        decreases a@.len() - i as int
    {
        if a[i] != 0.0 {
            indices.push(i);
        }
        i += 1;
    }
    indices
}
// </vc-code>

}
fn main() {}