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
pub fn swap(a: &mut Vec<int>, i: int, j: int)
    requires(
        0 <= i < old(a).len() && 0 <= j < old(a).len()
    )
    ensures(
        a@ == old(a)@.update(i as nat, old(a)@[j as nat]).update(j as nat, old(a)@[i as nat]),
        valid_permut(a@, old(a)@)
    )
{
}

// We then define "sorted" (by increasing order):
spec fn sorted(a: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

// Now, the lol sort algorithm:
// (Some invariants were tricky to find, but Dafny was smart enough otherwise)
pub fn lol_sort(a: &mut Vec<int>)
    ensures(
        valid_permut(a@, old(a)@),
        sorted(a@)
    )
{
}

pub fn main() {
}

}