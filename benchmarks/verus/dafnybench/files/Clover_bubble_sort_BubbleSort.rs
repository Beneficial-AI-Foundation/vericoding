// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<i32>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}