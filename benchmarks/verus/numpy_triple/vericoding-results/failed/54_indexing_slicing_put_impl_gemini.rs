// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added requires clauses to fix termination and index-out-of-bounds errors. */
spec fn updated_value(a: Seq<f64>, ind: Seq<usize>, v: Seq<f64>, k: int, idx: int) -> f64
    requires
        0 <= k <= ind.len(),
        ind.len() == v.len(),
        0 <= idx < a.len(),
        forall|i: int| 0 <= i < ind.len() ==> ind[i] < a.len(),
    decreases k
{
    if k == 0 {
        a[idx]
    } else {
        if idx == ind[k-1] {
            v[k-1]
        } else {
            updated_value(a, ind, v, k - 1, idx)
        }
    }
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
/* code modified by LLM (iteration 5): no changes; fixes are in the helper function. */
{
    let mut result = a.clone();
    let mut i: usize = 0;
    while i < ind.len()
        invariant
            0 <= i <= ind.len(),
            ind.len() == v.len(),
            (forall|j: int| 0 <= j < ind.len() ==> ind[j] < a.len()),
            a.len() == result.len(),
            forall|j: int| 0 <= j < a.len() ==> result[j] == updated_value(a@, ind@, v@, i as int, j),
        decreases ind.len() - i
    {
        let update_idx = ind[i];
        let update_val = v[i];
        result.set(update_idx, update_val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}