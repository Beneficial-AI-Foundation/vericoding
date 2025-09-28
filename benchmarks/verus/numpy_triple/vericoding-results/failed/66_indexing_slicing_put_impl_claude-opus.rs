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
    /* code modified by LLM (iteration 5): fixed invariants to properly track element updates */
    let mut result = a.clone();
    let mut i: usize = 0;
    
    while i < ind.len()
        invariant
            i <= ind.len(),
            i <= v.len(),
            result@.len() == a@.len(),
            ind.len() == v.len(),
            forall|k: int| 0 <= k < ind@.len() ==> (ind[k] as int) < (a@.len() as int),
            forall|k: int| 0 <= k < i ==> result@[ind[k] as int] == v@[k],
            forall|j: int| 0 <= j < result@.len() ==> 
                ((forall|k: int| 0 <= k < i ==> j != ind[k] as int) ==> 
                    ((forall|k: int| i <= k < ind@.len() ==> j != ind[k] as int) ==> result@[j] == a@[j])),
        decreases ind.len() - i
    {
        let idx = ind[i];
        let val = v[i];
        result.set(idx, val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}