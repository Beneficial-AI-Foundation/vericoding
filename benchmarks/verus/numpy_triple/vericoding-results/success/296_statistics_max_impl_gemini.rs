// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        /* Core property: result is the maximum element in the vector */
        exists|max_idx: int| 0 <= max_idx < a.len() &&
            result as int == a[max_idx as int] as int &&
            forall|i: int| 0 <= i < a.len() ==> a[i as int] as int <= result as int,
        /* Uniqueness: result is the first occurrence of the maximum */
        exists|first_max_idx: int| 0 <= first_max_idx < a.len() &&
            result as int == a[first_max_idx as int] as int &&
            (forall|i: int| 0 <= i < a.len() && a[i as int] as int == result as int ==> first_max_idx <= i) &&
            (forall|i: int| 0 <= i < a.len() ==> a[i as int] as int <= result as int),
        /* For constant vectors, max equals the constant */
        (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i as int] as int == a[j as int] as int) ==>
            result as int == a[0] as int,
        /* Sanity check: the maximum exists in the vector */
        exists|witness: int| 0 <= witness < a.len() && result as int == a[witness as int] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Track index of max to find the first occurrence. */
    let mut max_val = a[0];
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            0 <= (max_idx as int) < (i as int),
            max_val as int == a[max_idx as int] as int,
            forall|j: int| 0 <= j < (i as int) ==> a[j as int] as int <= max_val as int,
            forall|j: int| 0 <= j < (i as int) && a[j as int] as int == max_val as int ==> (max_idx as int) <= j,
        decreases a.len() - i
    {
        if a[i] > max_val {
            max_val = a[i];
            max_idx = i;
        }
        i = i + 1;
    }
    max_val
}
// </vc-code>


}
fn main() {}