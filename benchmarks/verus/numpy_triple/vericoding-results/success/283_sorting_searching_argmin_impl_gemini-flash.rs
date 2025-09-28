// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_argmin(a: Vec<i8>) -> (result: usize)
    requires a.len() > 0,
    ensures 
        result < a.len(),
        forall|j: int| 0 <= j < a@.len() ==> a@[result as int] <= a@[j],
        forall|j: int| 0 <= j < a@.len() && a@[j] == a@[result as int] ==> (result as int) <= j,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fix compilation errors related to indexing `Seq<i8>` using `@` and `usize` to `int` casting. */
    let mut min_val: i8 = a[0];
    let mut min_idx: usize = 0;
    let mut i: usize = 1;

    while i < a.len()
        invariant
            0 < a.len(),
            1 <= i,
            i <= a.len(),
            min_idx < i,
            min_idx < a.len(),
            forall|k: int| 0 <= k < i ==> a@[k] >= min_val,
            a@[min_idx as int] == min_val,
            forall|l: int| 0 <= l < i && a@[l] == a@[min_idx as int] ==> (min_idx as int) <= l,
        decreases a.len() - i
    {
        if a[i] < min_val {
            min_val = a[i];
            min_idx = i;
        } else if a[i] == min_val {
            // If values are equal, the first occurrence is already stored in min_idx.
            // No action needed as per the tie-breaking rule (first occurrence).
        }
        i = i + 1;
    }
    min_idx
}
// </vc-code>


}
fn main() {}