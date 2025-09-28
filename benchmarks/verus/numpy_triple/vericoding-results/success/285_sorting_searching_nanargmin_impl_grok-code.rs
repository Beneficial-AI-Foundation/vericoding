// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nanargmin(a: Vec<i8>) -> (result: usize)
    requires 
        a.len() > 0,
    ensures
        result < a.len(),
        forall|j: int| 0 <= j < a@.len() ==> a[result as int] <= a[j],
        forall|j: int| 0 <= j < result ==> a[j] > a[result as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type mismatches in loop invariants by using spec indexing with a@ and casting indices to int */
    let mut min_index: usize = 0;
    let mut min_val = a[0];
    let mut i = 1;
    while i < a.len()
        invariant
            i <= a.len(),
            0 <= min_index < i,
            min_val == a@[min_index as int],
            forall|j: int| 0 <= j < (i as int) ==> a@[min_index as int] <= a@[j],
            forall|j: int| 0 <= j < (min_index as int) ==> a@[j] > min_val,
        decreases a.len() - i
    {
        if a[i] < min_val {
            min_val = a[i];
            min_index = i;
        }
        i += 1;
    }
    min_index
}
// </vc-code>


}
fn main() {}