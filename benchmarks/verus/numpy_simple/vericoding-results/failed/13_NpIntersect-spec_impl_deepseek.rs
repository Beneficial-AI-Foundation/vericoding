// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix ghost code usage in exec context */
fn is_in_vec_exec(elem: i8, v: Vec<i8>) -> (found: bool)
    ensures
        found == exists|i: int| 0 <= i < v@.len() && v@[i] == elem,
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            forall|k: int| 0 <= k < i as int ==> v@[k] != elem,
        decreases v@.len() - i as int,
    {
        if v[i] == elem {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn intersect(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() < a.len() && result.len() < b.len(),
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < b@.len() ==> (
            (a@[i] == b@[j] ==> exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i]) &&
            (a@[i] != b@[j] ==> !exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i])
        )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use exec helper and fix type issues */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a@.len(),
            result@.len() <= i as int,
            forall|k: int| 0 <= k < result@.len() ==> exists|j: int| 0 <= j < b@.len() && result@[k] == b@[j],
            forall|k: int| 0 <= k < result@.len() ==> exists|j: int| 0 <= j < a@.len() && result@[k] == a@[j],
        decreases a@.len() - i as int,
    {
        let elem = a[i];
        let in_b = is_in_vec_exec(elem, b.clone());
        let in_result = is_in_vec_exec(elem, result.clone());
        if in_b && !in_result {
            result.push(elem);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}