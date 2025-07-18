use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: &[int], i: int, j: int) -> bool
{
    &&& 0 <= i <= j + 1 <= a.len()
    &&& forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
}

pub fn insertion_sort(a: &mut Vec<int>)
    ensures
        sorted_seg(a, 0, a.len() as int - 1),
        a@.to_multiset() == old(a)@.to_multiset(),
{
}

}