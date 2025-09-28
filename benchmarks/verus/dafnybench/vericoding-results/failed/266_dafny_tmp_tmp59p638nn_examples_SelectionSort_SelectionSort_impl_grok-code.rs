use vstd::prelude::*;

verus! {

spec fn ordered(a: Seq<int>, left: int, right: int) -> bool {
    &&& 0 <= left <= right <= a.len()
    &&& forall |i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// <vc-helpers>
spec fn is_min_index(a: Seq<int>, start: int, end: int, idx: int) -> bool {
    &&& start <= idx < end
    &&& forall |i: int| #![trigger] start <= i < end ==> a[idx] <= a[i]
    &&& start <= idx < end
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<int>)
    ensures 
        ordered(a@, 0, a.len() as int),
        a.len() == old(a).len(),
        a@.to_multiset() =~= old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
spec fn is_min_index(a: Seq<int>, start: int, end: int, idx: int) -> bool {
    &&& start <= idx < end
    &&& forall |i: int| #![trigger] start <= i < end ==> a[idx] <= a[i]
    &&& start <= idx < end
}
// </vc-code>

fn main() {}

}