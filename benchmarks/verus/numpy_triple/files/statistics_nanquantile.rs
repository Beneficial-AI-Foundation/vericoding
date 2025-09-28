// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn nanquantile(a: Vec<i8>, q: i8) -> (result: i8)
    requires 
        a.len() > 0,
        0 <= q <= 100,
    ensures
        /* Result is bounded by the elements */
        (forall|min_idx: int| 0 <= min_idx < a.len() ==> 
         (forall|j: int| 0 <= j < a.len() ==> a[min_idx] as int <= a[j] as int) ==> a[min_idx] as int <= result as int),
        (forall|max_idx: int| 0 <= max_idx < a.len() ==>
         (forall|j: int| 0 <= j < a.len() ==> a[j] as int <= a[max_idx] as int) ==> result as int <= a[max_idx] as int),
        /* For q=0, result is the minimum element */
        (q == 0) ==> 
            (forall|min_idx: int| 0 <= min_idx < a.len() ==>
             (forall|j: int| 0 <= j < a.len() ==> a[min_idx] as int <= a[j] as int) ==>
             result == a[min_idx]),
        /* For q=100, result is the maximum element */
        (q == 100) ==>
            (forall|max_idx: int| 0 <= max_idx < a.len() ==>
             (forall|j: int| 0 <= j < a.len() ==> a[j] as int <= a[max_idx] as int) ==>
             result == a[max_idx])
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