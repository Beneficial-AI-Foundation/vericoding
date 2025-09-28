// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn put(a: Vec<f64>, ind: Vec<usize>, v: Vec<f64>) -> (result: Vec<f64>)
    requires 
        ind.len() == v.len(),
        forall|i: int| 0 <= i < ind@.len() ==> (ind[i] as int) < (a@.len() as int),
    ensures
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < ind@.len() ==> result@[ind[i] as int] == v@[i],
        forall|j: int| 0 <= j < result@.len() ==> 
            (forall|i: int| 0 <= i < ind@.len() ==> j != ind[i] as int) ==> result@[j] == a@[j],
        ind@.len() == 0 ==> result@ == a@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed Vector set to functional style, used while loop with invariants, and added proof assertions for bounds */
    let mut result = a.clone();
    let mut j = 0;
    while j < ind.len()
        invariant
            0 <= j <= ind.len(),
            result@.len() == a@.len(),
            forall|i: int| 0 <= i < j ==> result@[ind[i] as int] == v@[i],
        decreases ind.len() - j
    {
        proof {
            assert(j < ind.len());
            let idx_i = ind@[j as int] as int;
            assert(0 <= idx_i < a@.len());
            assert(j as int < v@.len());
        }
        let idx = ind[j];
        result = result.set(idx, v[j]);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}