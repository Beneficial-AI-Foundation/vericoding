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

predicate valid_permut(a: seq<int>, b: seq<int>)
  requires |a| == |b|
{
  multiset(a) == multiset(b)
}

// This is a swap-based sorting algorithm, so permutedness is trivial:
// note that: if i == j, the spec just says a[..] remains the same.

// We then define "sorted" (by increasing order):
predicate sorted(a: seq<int>)
{
  forall i, j | 0 <= i <= j < |a| :: a[i] <= a[j]
}


// Now, the lol sort algorithm:
// (Some invariants were tricky to find, but Dafny was smart enough otherwise)

// <vc-helpers>
// Helper lemma to prove that swapping preserves multisets
lemma SwapPreservesMultiset(s: seq<int>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
  var s' := s[i := s[j]][j := s[i]];
  
  if i == j {
    assert s' == s;
  } else {
    // The multiset remains the same after swapping
    assert multiset(s') == multiset(s);
  }
}
// </vc-helpers>

// <vc-spec>
method swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[..] == old(a[..]) [i := old(a[j])] [j := old(a[i])]
  ensures valid_permut(a[..], old(a[..]))
// </vc-spec>
// <vc-code>
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
  
  // Prove the multiset preservation
  SwapPreservesMultiset(old(a[..]), i, j);
}
// </vc-code>

