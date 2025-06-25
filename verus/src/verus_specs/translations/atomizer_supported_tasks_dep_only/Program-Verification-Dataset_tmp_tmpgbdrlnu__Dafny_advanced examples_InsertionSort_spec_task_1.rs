use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int], start: int, end: int) -> bool
    recommends
        0 <= start <= end <= a.len(),
{
    forall|j: int, k: int| start <= j < k < end ==> a[j] <= a[k]
}

pub fn insertion_sort(a: &mut Vec<int>)
    requires(a.len() > 1)
    ensures(sorted(a, 0, a.len() as int))
{
}

}