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
    /* code modified by LLM (iteration 5): fixed comma syntax in forall expression within invariant */
    let mut result = a.clone();
    let mut i = 0;
    while i < ind.len()
        invariant
            i <= ind.len(),
            result.len() == a.len(),
            forall|k: int| 0 <= k < i ==> (0 <= ind[k] as int && ind[k] as int < result@.len()),
            forall|k: int| 0 <= k < i ==> 0 <= k < v@.len(),
            forall|k: int| 0 <= k < i ==> result@[ind[k] as int] == v@[k],
            forall|j: int| 0 <= j < result@.len() ==> 
                (forall|k: int| 0 <= k < i ==> j != ind[k] as int) ==> result@[j] == a@[j],
        decreases ind.len() - i
    {
        proof {
            assert(i < ind.len());
            assert(0 <= i < ind@.len());
            assert(ind[i] as int < a@.len());
            assert(ind[i] as int < result@.len());
            assert(i < v@.len());
        }
        result.set(ind[i], v[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}