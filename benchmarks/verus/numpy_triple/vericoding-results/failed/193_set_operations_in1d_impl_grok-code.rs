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
        forall|i: int| 0 <= i < ar1@.len() ==> 
            result@[i] == exists|j: int| 0 <= j < ar2@.len() && ar1@[i] == ar2@[j]
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): fixed invariants by adding bounds to forall and exists, and added assert to ensure index bounds for Vec access */
    let mut result: Vec<bool> = Vec::with_capacity(ar1.len());
    let mut i: usize = 0;
    while i < ar1.len()
        invariant
            0 <= (i as int) <= ar1@.len(),
            result@.len() == (i as int),
            forall|k: int| 0 <= k < (i as int) ==> 
                (result@[k] <==> exists|j: int| 0 <= j < ar2@.len() && ar1@[k] == ar2@[j])
        decreases ar1.len() - (i as int)
    {
        proof { assert(i < ar1.len()); }
        let mut found = false;
        let mut j: usize = 0;
        while j < ar2.len()
            invariant
                0 <= (j as int) <= ar2@.len(),
                !found ==> forall|jj: int| (0 <= jj < (j as int) && 0 <= jj < ar2@.len()) ==> ar1@[i as int] != ar2@[jj],
                found ==> exists|jj: int| (0 <= jj < (j as int) && 0 <= jj < ar2@.len()) && ar1@[i as int] == ar2@[jj],
                !found || (found == exists|any_j: int| 0 <= any_j < ar2@.len() && ar1@[i as int] == ar2@[any_j])
            decreases ar2.len() - (j as int)
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