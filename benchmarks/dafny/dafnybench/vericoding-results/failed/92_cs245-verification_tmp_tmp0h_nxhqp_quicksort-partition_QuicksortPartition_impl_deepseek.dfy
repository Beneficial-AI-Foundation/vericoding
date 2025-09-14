// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...

/* The annotations and implied proofs are left for you.
   I might do them later on next week. */

// <vc-helpers>
lemma {:induction false} SwapPreservesMultiset<T>(X: array<T>, i: int, j: int)
  modifies X
  requires 0 <= i < X.Length && 0 <= j < X.Length
  ensures multiset(X[..]) == multiset(old(X[..]))
{
  var oldSeq := X[..];
  var temp := X[i];
  X[i] := X[j];
  X[j] := temp;
  assert multiset(X[..]) == multiset(oldSeq);
}

lemma {:induction false} PartitionInvariant<T(==)>(X: array<T>, a: int, b: int, p: T)
  requires X != null
  requires 0 <= a <= b <= X.Length
  requires forall x :: 0 <= x < a ==> X[x] <= p
  requires forall x :: a <= x < b ==> X[x] > p
{
}
// </vc-helpers>

// <vc-spec>
method QuicksortPartition(X: array<int>, n: int, p: int) returns (a: int, b: int)
modifies X;
/*Pre-Condition*/   requires X.Length>=1 && n == X.Length;
/*Post-Condition*/  ensures b>=n;
                    ensures forall x:: 0<=x<a<n ==> X[x] <= p;
                    ensures forall x:: a==n || (0<=a<=x<n ==> X[x] > p);
                    ensures multiset(X[..])==multiset(old(X[..]))           //This says the new X is a permutation of our old version of X.
// </vc-spec>
// <vc-code>
{
  a := 0;
  b := 0;
  
  while b < n
    invariant 0 <= a <= b <= n
    invariant forall x :: 0 <= x < a ==> X[x] <= p
    invariant forall x :: a <= x < b ==> X[x] > p
    invariant multiset(X[..]) == multiset(old(X[..]))
  {
    if X[b] <= p {
      SwapPreservesMultiset(X, a, b);
      a := a + 1;
    }
    b := b + 1;
  }
}
// </vc-code>

