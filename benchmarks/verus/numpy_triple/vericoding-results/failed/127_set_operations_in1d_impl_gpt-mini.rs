// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for membership of an element in a vector */
spec fn exists_in<T: PartialEq>(x: T, v: Vec<T>) -> bool { exists|i: int| 0 <= i < v.len() && v@[i] == x }
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
    /* code modified by LLM (iteration 5): implement in1d by nested loops with invariants and decreases */
    let mut result: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < ar1.len()
        invariant 0 <= i;
        invariant i <= ar1.len();
        invariant result.len() == i;
        invariant forall|k: int| 0 <= k < i ==> result@[k] == exists|j: int| 0 <= j < ar2.len() && ar1@[k] == ar2@[j];
        decreases ar1.len() - i
    {
        let mut j: int = 0;
        let mut found: bool = false;
        while j < ar2.len()
            invariant 0 <= j;
            invariant j <= ar2.len();
            invariant (found ==> exists|jj: int| 0 <= jj < j && ar1@[i] == ar2@[jj]);
            invariant (!found ==> forall|jj: int| 0 <= jj < j ==> ar1@[i] != ar2@[jj]);
            decreases ar2.len() - j
        {
            if ar1[i] == ar2[j] {
                found = true;
                j = ar2.len();
            } else {
                j = j + 1;
            }
        }
        result.push(found);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}