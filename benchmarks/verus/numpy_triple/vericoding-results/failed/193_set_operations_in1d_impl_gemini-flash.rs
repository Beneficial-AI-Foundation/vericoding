// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add a helper predicate to formalize the existence check */
pub closed spec fn exists_in_array<T: PartialEq>(element: T, arr: &Vec<T>) -> bool {
    exists|j: int| 0 <= j < arr@.len() && arr@[j] == element
}
// </vc-helpers>

// <vc-spec>
fn in1d<T: PartialEq>(ar1: Vec<T>, ar2: Vec<T>) -> (result: Vec<bool>)
    ensures 
        result.len() == ar1.len(),
        forall|i: int| 0 <= i < ar1@.len() ==> 
            result@[i] == exists|j: int| 0 <= j < ar2@.len() && ar1@[i] == ar2@[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed `as nat` casts in runtime code */
{
    let mut result: Vec<bool> = Vec::new();
    result.reserve(ar1.len());
    let ar1_seq = ar1.view();
    let ar2_seq = ar2.view();
    for i in 0..ar1.len()
        invariant 
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> result@[idx] == exists_in_array(ar1_seq.index(idx as nat), &ar2),
    {
        let mut found = false;
        for j in 0..ar2.len()
            invariant
                found == (exists|k: int| 0 <= k < j && ar1_seq.index(i as nat) == ar2_seq.index(k as nat)),
                j <= ar2.len(),
        {
            if ar1@[i] == ar2@[j] {
                found = true;
                break;
            }
        }
        result.push(found);
    }
    result
}
// </vc-code>

}
fn main() {}