//ATOM
// By `lol sort` here, I refer to a seemingly-broken sorting algorithm,
// which actually somehow manages to work perfectly:
//
// for i in 0..n
//  for j in 0..n
//   if i < j
//    swap a[i], a[j]
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

//ATOM

// We then define "sorted" (by increasing order):
predicate sorted(a: seq<int>)
{
 forall i, j | 0 <= i <= j < |a| :: a[i] <= a[j]
}

//ATOM

// This is a swap-based sorting algorithm, so permutedness is trivial:
// note that: if i == j, the spec just says a[..] remains the same.
method swap(a: array<int>, i: int, j: int)
 requires 0 <= i < a.Length && 0 <= j < a.Length
 modifies a
 ensures a[..] == old(a[..]) [i := old(a[j])] [j := old(a[i])]
 ensures valid_permut(a[..], old(a[..]))
{
  /* code modified by LLM (iteration 1): replaced assume statements with actual swap implementation */
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}

//IMPL lol_sort
// Now, the lol sort algorithm:
// (Some invariants were tricky to find, but Dafny was smart enough otherwise)
method lol_sort(a: array<int>)
 modifies a
 ensures valid_permut(a[..], old(a[..]))
 ensures sorted(a[..])
{
  var orig := a[..];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant valid_permut(a[..], orig)
    invariant forall p, q | 0 <= p < i && p <= q < a.Length :: a[p] <= a[q]
  {
    var j := 0;
    while j < a.Length
      invariant 0 <= j <= a.Length
      invariant valid_permut(a[..], orig)
      invariant forall p, q | 0 <= p < i && p <= q < a.Length :: a[p] <= a[q]
      invariant forall q | i <= q < j :: a[i] <= a[q]
    {
      if i < j && a[i] > a[j] {
        swap(a, i, j);
      }
      j := j + 1;
    }
    i := i + 1;
  }
}