// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn scientific_vec_copy(a: Vec<f64>) -> (result: Vec<f64>) {
    a.clone()
}
// </vc-helpers>

// <vc-spec>
fn put(a: Vec<f64>, ind: Vec<usize>, v: Vec<f64>) -> (result: Vec<f64>)
    requires 
        ind.len() == v.len(),
        forall|i: int| 0 <= i < ind.len() ==> ind[i] < a.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < ind.len() ==> result[ind[i] as int] == v[i],
        forall|j: int| 0 <= j < result.len() ==> 
            (forall|i: int| 0 <= i < ind.len() ==> j != ind[i]) ==> result[j] == a[j],
        ind.len() == 0 ==> result@ == a@,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop invariants and preconditions */
{
    let mut result_vec = scientific_vec_copy(a);

    let mut i: usize = 0;
    while i < ind.len()
        invariant 
            0 <= i as int <= ind.len() as int,
            result_vec.len() == a.len(),
            forall|k: int| 0 <= k < i as int ==> #[trigger] result_vec[ind[k] as int] == v[k],
            forall|j: int| 0 <= j < result_vec.len() as int ==> 
                (forall|k: int| 0 <= k < i as int ==> #[trigger] j != ind[k] as int) ==> result_vec[j] == a[j],
            ind.len() == v.len(),
            forall|k: int| 0 <= k < i as int ==> ind[k] < a.len(),
        decreases ind.len() - i
    {
        let idx = ind[i];
        let val = v[i];
        
        assert(i < v.len()); // Precondition for v[i]
        assert(idx < result_vec.len()); // Precondition for result_vec.set(idx, val)

        result_vec.set(idx, val);
        i = i + 1;
    }

    result_vec
}
// </vc-code>

}
fn main() {}