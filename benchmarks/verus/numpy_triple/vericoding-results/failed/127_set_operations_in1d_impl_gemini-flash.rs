// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected type casting errors. */
fn find_in_ar2<T: PartialEq>(val: T, ar2: &Vec<T>) -> (b: bool)
    ensures b == exists|j: int| 0 <= j < ar2.len() && val == ar2@[j]
{
    let mut found = false;
    let mut k: usize = 0;
    while k < ar2.len()
        invariant
            0 <= k && k <= ar2.len(),
            found == (exists|j: int| 0 <= j && (j as usize) < k && val == ar2@[j])
    {
        if val == ar2@[k] {
            found = true;
        }
        k = k + 1;
    }
    found
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
/* code modified by LLM (iteration 5): Corrected type casting errors. */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < ar1.len()
        invariant
            0 <= i && i <= ar1.len(),
            result.len() == i,
            forall|k: int| 0 <= k && (k as usize) < i ==> result@[k] == exists|j: int| 0 <= j && (j as usize) < ar2.len() && ar1@[k] == ar2@[j]
    {
        let val_in_ar2 = find_in_ar2(ar1@[i], &ar2);

        result.push(val_in_ar2);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}