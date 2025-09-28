// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nanmax(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        /* Case 1: If there exists at least one element, the result is from the vector */
        (exists|max_idx: int| 
            0 <= max_idx < a.len() &&
            result as int == a[max_idx] as int) &&
        /* Case 2: Result is maximum among all elements */
        (forall|j: int| 0 <= j < a.len() ==> a[j] as int <= result as int) &&
        /* Case 3: Result exists in the vector */
        (exists|witness: int| 0 <= witness < a.len() && result as int == a[witness] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed sequence indexing syntax and variable initialization */
    let mut i: usize = 1;
    let mut result: i8 = a[0];

    while i < a.len()
        invariant
            1 <= i as int <= a.len() as int,
            exists|idx: int| 0 <= idx < i as int && result as int == a[idx] as int,
            forall|j: int| 0 <= j < i as int ==> a[j] as int <= result as int,
        decreases a.len() - i
    {
        if a[i] > result {
            result = a[i];
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}