use vstd::prelude::*;

verus! {

// By `lol sort` here, I refer to a seemingly-broken sorting algorithm,
// which actually somehow manages to work perfectly:
//
// for i in 0..n
//   for j in 0..n
//     if i < j
//       swap a[i], a[j]
//
// It is perhaps the simpliest sorting algorithm to "memorize",
// even "symmetrically beautiful" as if `i` and `j` just played highly
// similar roles. And technically it's still O(n^2) time lol...
//
// Proving its correctness is tricky (interesting) though.

// Successfully verified with Verus



// We define "valid permutation" using multiset:

spec fn valid_permut(a: Seq<int>, b: Seq<int>) -> bool
    recommends a.len() == b.len()
{
    a.to_multiset() == b.to_multiset()
}

// This is a swap-based sorting algorithm, so permutedness is trivial:
// note that: if i == j, the spec just says a[..] remains the same.

// We then define "sorted" (by increasing order):
spec fn sorted(a: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}


// Now, the lol sort algorithm:
// (Some invariants were tricky to find, but Verus was smart enough otherwise)

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap(a: &mut Vec<int>, i: usize, j: usize)
    requires 
        i < old(a).len(),
        j < old(a).len(),
    ensures 
        a.len() == old(a).len(),
        a@ == old(a)@.update(i as int, old(a)@[j as int]).update(j as int, old(a)@[i as int]),
        valid_permut(a@, old(a)@),
// </vc-spec>
// <vc-code>
{
    assume(false);
}
// </vc-code>


fn main() {
}

}