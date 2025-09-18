// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed type errors in indexing operations */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < ar1.len()
        invariant 
            0 <= i as int <= ar1.len() as int,
            result.len() == i,
            forall|k: int| 0 <= k < (i as int) ==> 
                result@[k] == exists|j: int| 0 <= j < ar2.len() as int && ar1@[k] == ar2@[j]
    {
        let mut found = false;
        let mut j: usize = 0;
        while j < ar2.len()
            invariant 
                0 <= j as int <= ar2.len() as int,
                found ==> exists|k: int| 0 <= k < (j as int) && ar1@[i as int] == ar2@[k],
                !found ==> forall|k: int| 0 <= k < (j as int) ==> ar1@[i as int] != ar2@[k]
        {
            if ar1[i] == ar2[j] {
                found = true;
            }
            j += 1;
        }
        result.push(found);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}