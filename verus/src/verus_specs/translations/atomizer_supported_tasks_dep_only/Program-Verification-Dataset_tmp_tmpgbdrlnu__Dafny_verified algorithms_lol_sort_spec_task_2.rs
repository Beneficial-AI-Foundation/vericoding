use vstd::prelude::*;

verus! {

spec fn valid_permut(a: Seq<int>, b: Seq<int>) -> bool
    recommends a.len() == b.len()
{
    a.to_multiset() == b.to_multiset()
}

pub fn swap(a: &mut Vec<int>, i: usize, j: usize)
    requires 
        0 <= i < old(a).len() && 0 <= j < old(a).len(),
        a.len() == old(a).len()
    ensures
        a@[i as int] == old(a)@[j as int],
        a@[j as int] == old(a)@[i as int],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a@[k] == old(a)@[k],
        valid_permut(a@, old(a)@)
{
}

spec fn sorted(a: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

pub fn lol_sort(a: &mut Vec<int>)
    ensures
        valid_permut(a@, old(a)@),
        sorted(a@)
{
}

}