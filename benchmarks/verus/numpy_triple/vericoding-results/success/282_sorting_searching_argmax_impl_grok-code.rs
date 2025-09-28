// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added invariant to ensure max_idx is the smallest index among equal values */
fn find_max_index(a: &[i8]) -> (result: usize)
    requires a@.len() > 0
    ensures
        0 <= result < a@.len(),
        forall|j: int| 0 <= j < a@.len() ==> a@[j] <= a@[result as int],
        forall|j: int| 0 <= j < a@.len() && a@[j] == a@[result as int] ==> result <= j as usize,
{
    let mut max_val = a[0];
    let mut max_idx = 0;
    let mut i = 1;
    while i < a.len()
        invariant
            0 <= max_idx < a@.len(),
            0 < i as int <= a@.len(),
            forall|k: int| 0 <= k < i as int ==> a@[k] <= max_val,
            forall|k: int| 0 <= k < i as int && a@[k] == max_val ==> max_idx <= k as usize,
            forall|k: int| 0 <= k < max_idx ==> a@[k] != max_val,
            a@[max_idx as int] == max_val,
        decreases (a@.len() - i as int)
    {
        if a[i] > max_val {
            max_val = a[i];
            max_idx = i;
        }
        i += 1;
    }
    max_idx
}
// </vc-helpers>

// <vc-spec>
fn argmax(a: Vec<i8>) -> (result: usize)
    requires a.len() > 0,
    ensures 
        result < a.len(),
        forall|j: int| 0 <= j < a@.len() ==> a@[j] <= a@[result as int],
        forall|j: int| 0 <= j < a@.len() && a@[j] == a@[result as int] ==> result <= j as usize,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): kept existing implementation */
{
    let result = find_max_index(&a);
    result
}
// </vc-code>

}
fn main() {}