use vstd::prelude::*;

verus! {

// We define "valid permutation" using multiset:
spec fn valid_permut(a: Seq<int>, b: Seq<int>) -> bool
    recommends a.len() == b.len()
{
    a.to_multiset() == b.to_multiset()
}

// This is a swap-based sorting algorithm, so permutedness is trivial:
// note that: if i == j, the spec just says a[..] remains the same.
pub fn swap(a: &mut Vec<int>, i: usize, j: usize)
    requires 0 <= i < old(a).len() && 0 <= j < old(a).len()
    ensures a@ == old(a)@.update(i as int, old(a)[j as int]).update(j as int, old(a)[i as int])
    ensures valid_permut(a@, old(a)@)
{
}

}