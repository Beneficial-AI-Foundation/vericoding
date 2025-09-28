// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argmin(a: Vec<i8>) -> (result: usize)
    requires a.len() > 0,
    ensures
        result < a.len(),
        forall|j: int| 0 <= j < a.len() ==> a[result as int] <= a[j],
        forall|k: int| 0 <= k < result ==> a[k] > a[result as int],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed type mismatch in invariant by converting min_index to int for vector indexing */
{
    let mut min_index = 0;
    let mut min_value = a[0];
    let mut i = 1;
    while i < a.len()
        invariant
            0 <= min_index as int,
            min_index < a.len(),
            min_index < i,
            min_value == a[min_index as int],
            forall|j: int| 0 <= j < i as int ==> a[min_index as int] <= a[j],
            forall|k: int| 0 <= k < min_index as int ==> a[k] > a[min_index as int],
        decreases a.len() - i,
    {
        if a[i] < min_value {
            min_index = i;
            min_value = a[i];
        }
        i += 1;
    }
    min_index
}
// </vc-code>


}
fn main() {}