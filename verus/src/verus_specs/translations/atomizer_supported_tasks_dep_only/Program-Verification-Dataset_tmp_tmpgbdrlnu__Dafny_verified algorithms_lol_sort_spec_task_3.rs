use vstd::prelude::*;

verus! {

spec fn valid_permut(a: Seq<int>, b: Seq<int>) -> bool
    recommends a.len() == b.len()
{
    a.to_multiset() == b.to_multiset()
}

pub fn swap(a: &mut Vec<int>, i: int, j: int)
    requires 
        0 <= i < old(a).len(),
        0 <= j < old(a).len(),
    ensures
        a@ == old(a)@.update(i as nat, old(a)@[j as nat]).update(j as nat, old(a)@[i as nat]),
        valid_permut(a@, old(a)@),
{
}

spec fn sorted(a: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

pub fn lol_sort(a: &mut Vec<int>)
    ensures
        valid_permut(a@, old(a)@),
        sorted(a@),
{
}

pub fn main()
{
}

}