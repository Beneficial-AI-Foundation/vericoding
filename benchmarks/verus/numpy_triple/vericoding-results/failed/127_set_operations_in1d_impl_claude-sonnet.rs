// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper function to check element membership */
spec fn contains<T: PartialEq>(ar: Vec<T>, element: T) -> bool {
    exists|j: int| 0 <= j < ar.len() && ar[j] == element
}
// </vc-helpers>

// <vc-spec>
fn in1d<T: PartialEq>(ar1: Vec<T>, ar2: Vec<T>) -> (result: Vec<bool>)
    ensures 
        result.len() == ar1.len(),
        forall|i: int| 0 <= i < ar1.len() ==> 
            result[i] == exists|j: int| 0 <= j < ar2.len() && ar1[i] == ar2[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch by using int indexing */
    let mut result = Vec::new();
    for i in 0..ar1.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> 
                result[k] == exists|j: int| 0 <= j < ar2.len() && ar1[k] == ar2[j]
    {
        let mut found = false;
        for j in 0..ar2.len()
            invariant
                i < ar1.len(),
                found == exists|k: int| 0 <= k < j as int && ar1[i as int] == ar2[k]
        {
            if ar1[i as int] == ar2[j as int] {
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