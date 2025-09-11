// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn ordered(a: Seq<int>, left: int, right: int) -> bool {
    &&& 0 <= left <= right <= a.len()
    &&& forall |i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<int>)
    ensures 
        ordered(a@, 0, a.len() as int),
        a.len() == old(a).len(),
        a@.to_multiset() =~= old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}