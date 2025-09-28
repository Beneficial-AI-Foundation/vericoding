// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Converted to ghost function with proper int/nat handling */
#[verifier::spec]
fn vec_index_not_in_list(a: Vec<f64>, ind: Vec<usize>, j: int) -> (result: bool)
    requires
        0 <= j < a@.len() as int,
    ensures
        result == (forall|i: int| 0 <= i < ind@.len() ==> j != ind[i] as int),
{
    let mut i: int = 0;
    while i < ind@.len()
        invariant
            0 <= i <= ind@.len(),
            forall|k: int| 0 <= k < i ==> j != ind[k] as int,
        decreases ind@.len() - i,
    {
        if j == ind[i] as int {
            return false;
        }
        i += 1;
    }
    true
}

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
    /* code modified by LLM (iteration 5): Fixed ghost variable access and type conversion issues */
    let mut result = a;
    let mut idx: int = 0;
    while idx < ind@.len()
        invariant
            0 <= idx <= ind@.len(),
            result@.len() == a@.len(),
            forall|i: int| 0 <= i < idx ==> result@[ind[i] as int] == v@[i],
            forall|j: int| 0 <= j < result@.len() ==> 
                vec_index_not_in_list(result, ind, j) ==> result@[j] == a@[j],
        decreases ind@.len() - idx,
    {
        let pos_ghost: int = ind@[idx] as int;
        let pos = ind[idx as usize];
        result = result.update(pos, v[idx as usize]);
        idx += 1;
    }
    result
}
// </vc-code>

}
fn main() {}