use vstd::prelude::*;

verus! {

pub fn bubble_sort(a: &mut Array2<int>)
    requires
        old(a).len1() == 2,
    ensures
        a.len1() == 2,
        sorted(a, 0, a.len0() - 1),
{
}

pub open spec fn sorted(a: &Array2<int>, l: int, u: int) -> bool
    recommends
        a.len1() == 2,
{
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len0() ==> a[i][1] <= a[j][1]
}

}