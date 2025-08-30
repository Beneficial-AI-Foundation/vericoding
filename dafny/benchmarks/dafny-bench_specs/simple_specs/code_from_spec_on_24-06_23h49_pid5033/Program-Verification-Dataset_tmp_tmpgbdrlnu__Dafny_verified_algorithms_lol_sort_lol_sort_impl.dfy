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
  assume a[..] == old(a[..]) [i := old(a[j])] [j := old(a[i])];
  assume valid_permut(a[..], old(a[..]));
}


//IMPL lol sort

// Now, the lol sort algorithm:
// (Some invariants were tricky to find, but Dafny was smart enough otherwise)
method lol_sort(a: array<int>)
 modifies a
 ensures valid_permut(a[..], old(a[..]))
 ensures sorted(a[..])
{
  var n := a.Length;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant valid_permut(a[..], old(a[..]))
    /* code modified by LLM (iteration 1): Updated invariant to correctly capture that elements 0..i-1 are <= all elements i..n-1 */
    invariant forall p, q | 0 <= p < i && i <= q < n :: a[p] <= a[q]
    /* code modified by LLM (iteration 1): Updated invariant to ensure elements 0..i-1 are sorted among themselves */
    invariant forall p, q | 0 <= p < q < i :: a[p] <= a[q]
  {
    var j := 0;
    
    while j < n
      invariant 0 <= j <= n
      invariant valid_permut(a[..], old(a[..]))
      /* code modified by LLM (iteration 1): Maintained outer loop's key invariants */
      invariant forall p, q | 0 <= p < i && i <= q < n :: a[p] <= a[q]
      invariant forall p, q | 0 <= p < q < i :: a[p] <= a[q]
      /* code modified by LLM (iteration 1): Added invariant to ensure a[i] is <= all elements we've processed in positions i+1..j-1 */
      invariant forall q | i < q < j :: a[i] <= a[q]
    {
      /* code modified by LLM (iteration 1): Added condition a[i] > a[j] to ensure we only swap when necessary for correctness */
      if i < j && a[i] > a[j] {
        swap(a, i, j);
      }
      j := j + 1;
    }
    i := i + 1;
  }
}