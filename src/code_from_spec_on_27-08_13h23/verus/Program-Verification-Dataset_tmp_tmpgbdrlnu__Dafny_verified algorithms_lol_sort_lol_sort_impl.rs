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

// Successfully verified with [Dafny 3.3.0.31104] in about 5 seconds.



// We define "valid permutation" using multiset:

spec fn valid_permut(a: Seq<int>, b: Seq<int>) -> bool
    recommends a.len() == b.len()
{
    a.to_multiset() == b.to_multiset()
}

// This is a swap-based sorting algorithm, so permutedness is trivial:
// note that: if i == j, the spec just says a[..] remains the same.
fn swap(a: &mut Vec<int>, i: usize, j: usize)
    requires 
        i < old(a).len(),
        j < old(a).len(),
    ensures
        a.len() == old(a).len(),
        a@ == old(a)@.update(i as int, old(a)[j as int]).update(j as int, old(a)[i as int]),
        valid_permut(a@, old(a)@),
{
    assume(false);
}

// We then define "sorted" (by increasing order):
spec fn sorted(a: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}


// Now, the lol sort algorithm:
// (Some invariants were tricky to find, but Verus was smart enough otherwise)

// <vc-helpers>
spec fn count_less_equal(s: Seq<int>, val: int, start: int, end: int) -> int
    recommends 0 <= start <= end <= s.len()
    decreases end - start
{
    if start == end {
        0
    } else {
        let cnt = if s[start] <= val { 1 } else { 0 };
        cnt + count_less_equal(s, val, start + 1, end)
    }
}

spec fn num_inversions(s: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= s.len()
    decreases j - i
{
    if i == j {
        0
    } else {
        let inv = if i < j - 1 && s[i] > s[j - 1] { 1 } else { 0 };
        inv + num_inversions(s, i, j - 1)
    }
}

proof fn lemma_swap_decreases_inversions(a: Seq<int>, i: int, j: int)
    requires
        0 <= i < j < a.len(),
        a[i] > a[j],
    ensures
        num_inversions(a, i, j) >= 1,
        num_inversions(a.update(i, a[j]).update(j, a[i]), i, j) < num_inversions(a, i, j),
{
    assert(num_inversions(a, i, j) >= 1);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn lol_sort(a: &mut Vec<int>)
    ensures 
        valid_permut(a@, old(a)@),
        sorted(a@),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn lol_sort(a: &mut Vec<int>)
    ensures 
        valid_permut(a@, old(a)@),
        sorted(a@),
{
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            valid_permut(a@, old(a)@),
            forall|k: int| 0 <= k < i ==> forall|l: int| k < l < n ==> a@[k] <= a@[l],
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                0 <= i < n,
                i <= j <= n,
                valid_permut(a@, old(a)@),
                forall|k: int| 0 <= k < i ==> forall|l: int| k < l < n ==> a@[k] <= a@[l],
                forall|k: int| i < k < j ==> a@[i] <= a@[k],
        {
            if a[i] > a[j] {
                swap(a, i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}