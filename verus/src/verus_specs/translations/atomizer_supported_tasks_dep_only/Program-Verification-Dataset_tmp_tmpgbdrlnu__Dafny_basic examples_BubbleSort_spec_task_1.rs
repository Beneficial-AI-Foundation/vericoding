use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int], from: int, to: int) -> bool
    recommends
        0 <= from <= to <= a.len()
{
    forall|u: int, v: int| from <= u < v < to ==> a[u] <= a[v]
}

pub fn bubbleSort(a: &mut Vec<int>)
    requires(a.len() > 0)
    ensures(sorted(a, 0, a.len() as int))
    ensures(a@.to_multiset() == old(a)@.to_multiset())
{
}

}