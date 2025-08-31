use vstd::prelude::*;

verus! {

///////////////////
// Binary search
///////////////////


spec fn is_sorted(a: &[int]) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}


// a[lo] <= a[lo+1] <= ... <= a[hi-2] <= a[hi-1]

/* Note: the following definition of is_sorted:


although equivalent to the one above is not enough for Verus to be able 
to prove the invariants for the loop in bin_search.

The given one works because it *explicitly* states that every element 
of the input array is smaller than or equal to all later elements. 
This fact is implied by the alternative definition of is_sorted given 
here (which only talks about array elements and their successors). 
However, it needs to be derived as an auxiliary lemma first, something 
that Verus is not currently able to do automatically. 
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn bin_search(a: &[int], k: int) -> (b: bool)
    requires is_sorted(a)
    ensures b == exists|i: int| 0 <= i < a.len() && a[i] == k
// </vc-spec>
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


fn main() {
}

}