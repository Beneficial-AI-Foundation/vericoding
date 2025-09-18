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
    /* code modified by LLM (iteration 5): Changed loop index types to int for spec compatibility and used index as usize for vector access to fix compilation errors like type mismatches, missing as_int, invalid assignments, and invalid casts. */
    let mut result = Vec::new();
    let mut i: int = 0;
    while i < ar1@.len()
        invariant
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] == exists|j: int| 0 <= j < ar2@.len() && ar1@[k] == ar2@[j]
        decreases ar1@.len() - i
    {
        let mut found = false;
        let mut m: int = 0;
        while m < ar2@.len()
            invariant
                found == exists|l: int| 0 <= l < m && ar1@[i] == ar2@[l]
            decreases ar2@.len() - m
        {
            if ar1[i as usize] == ar2[m as usize] {
                found = true;
            }
            m += 1;
        }
        result.push(found);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}