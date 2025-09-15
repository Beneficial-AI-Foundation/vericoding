// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary helper as `min_by_seq` exists */
// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        forall|i: int| 0 <= i < a.len() ==> result <= a[i],
        exists|i: int| 0 <= i < a.len() && result == a[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Simplified invariant without `min_by_seq` to address compilation error. */
{
    let mut result = a[0];
    let mut i = 1;

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            forall|j: int| 0 <= j < i ==> result <= a[j],
            exists|j: int| 0 <= j < i && result == a[j]
        decreases a.len() - i
    {
        if a[i] < result {
            result = a[i];
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}