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
/* code modified by LLM (iteration 3): use usize loop counter to avoid int conversion in non-ghost code */
{
    let mut result = a;
    let n = ind.len();
    let mut i: usize = 0;
    while i < n
        invariant 
            0 <= i as int <= n as int,
            result@.len() == a@.len(),
            forall|j: int| 0 <= j < i as int ==> result@[ (ind@[j] as int) ] == v@[j],
            forall|j: int| 0 <= j < result@.len() ==> 
                (forall|k: int| 0 <= k < i as int ==> j != (ind@[k] as int)) ==> result@[j] == a@[j],
        decreases n - i,
    {
        result[ind[i]] = v[i];
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}