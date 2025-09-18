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
    /* code modified by LLM (iteration 5): Removed erroneous spec sequence assignment causing compilation error; implemented vector initialization with standard library methods and index updates using invariants for memory safety and postcondition verification. */
    let mut result: Vec<f64> = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        result.push(a[i]);
    }
    proof {
        assert(result@ == a@);
    }
    let ind_seq = ind@;
    let v_seq = v@;
    for k in 0..ind.len()
        invariant
            result.len() == a.len(),
            forall|i: int| 0 <= i < ind.len() && i < k ==> result@[ind@[i] as int] == v@[i],
            forall|j: int| 0 <= j < result.len() ==> 
                (forall|i: int| 0 <= i < k ==> j != (ind@[i] as int)) ==> result@[j] == a@[j]
    {
        let idx: usize = ind[k];
        let val: f64 = v[k];
        result[idx] = val;
    }
    result
}
// </vc-code>

}
fn main() {}