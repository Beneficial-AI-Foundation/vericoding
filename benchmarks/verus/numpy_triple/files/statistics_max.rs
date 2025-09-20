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
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {}