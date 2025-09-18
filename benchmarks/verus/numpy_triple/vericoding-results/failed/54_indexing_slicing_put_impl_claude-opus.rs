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
        forall|i: int| 0 <= i < ind.len() ==> ind[i] < a.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < ind.len() ==> result[ind[i] as int] == v[i],
        forall|j: int| 0 <= j < result.len() ==> 
            (forall|i: int| 0 <= i < ind.len() ==> j != ind[i]) ==> result[j] == a[j],
        ind.len() == 0 ==> result@ == a@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed invalid trigger annotation from quantifier */
    let mut result = a;
    let mut i: usize = 0;
    while i < ind.len()
        invariant
            i <= ind.len(),
            result.len() == a.len(),
            ind.len() == v.len(),
            forall|j: int| 0 <= j < ind.len() ==> ind[j] < a.len(),
            forall|k: int| 0 <= k < i ==> result[ind[k] as int] == v[k],
            forall|j: int| 0 <= j < result.len() ==> {
                if exists|k: int| 0 <= k < i && ind[k] == j {
                    exists|k: int| 0 <= k < i && ind[k] == j && result[j] == v[k]
                } else {
                    result[j] == a[j]
                }
            },
        decreases ind.len() - i
    {
        result.set(ind[i], v[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}