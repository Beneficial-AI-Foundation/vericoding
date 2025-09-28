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
    /* code modified by LLM (iteration 2): Added decreases clauses to both loops */
    let mut result = Vec::new();
    let mut i = 0;
    while i < ar1.len()
        invariant
            0 <= i <= ar1.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> 
                result@[k] == exists|j: int| 0 <= j < ar2@.len() && ar1@[k] == ar2@[j],
        decreases ar1.len() - i
    {
        let mut found = false;
        let mut j = 0;
        while j < ar2.len()
            invariant
                0 <= j <= ar2.len(),
                found == exists|k: int| 0 <= k < j && ar1@[i as int] == ar2@[k],
            decreases ar2.len() - j
        {
            if ar1[i] == ar2[j] {
                found = true;
            }
            j = j + 1;
        }
        result.push(found);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}