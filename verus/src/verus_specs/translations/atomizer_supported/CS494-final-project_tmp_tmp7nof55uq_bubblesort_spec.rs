use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int], from: int, to: int) -> bool
{
    0 <= from <= to <= a.len() &&
    forall|x: int, y: int| from <= x < y < to ==> a[x as usize] <= a[y as usize]
}

spec fn pivot(a: &[int], to: int, pvt: int) -> bool
{
    0 <= pvt < to <= a.len() &&
    forall|x: int, y: int| 0 <= x < pvt < y < to ==> a[x as usize] <= a[y as usize]
}

pub fn BubbleSort(a: &mut Vec<int>)
    requires(a.len() > 0)
    ensures(sorted(a, 0, a.len() as int))
    ensures(a@.to_multiset() == old(a)@.to_multiset())
{
}

}