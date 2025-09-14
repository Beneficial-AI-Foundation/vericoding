// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...

/* The annotations and implied proofs are left for you.
   I might do them later on next week. */

// <vc-helpers>
lemma MultisetPreservation(X: array<int>, i: int, j: int)
  requires 0 <= i < X.Length && 0 <= j < X.Length
  ensures multiset(X[..]) == multiset(old(X[..]))
{
}

lemma PartitionInvariant(X: array<int>, n: int, p: int, a: int, k: int)
  requires 0 <= a <= k <= n <= X.Length
  requires forall x :: 0 <= x < a ==> X[x] <= p
  requires forall x :: a <= x < k ==> X[x] > p
  ensures forall x :: 0 <= x < a ==> X[x] <= p
  ensures forall x :: a <= x < k ==> X[x] > p
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
  var k := 0;
  
  while k < n
    invariant 0 <= a <= k <= n
    invariant forall x :: 0 <= x < a ==> X[x] <= p
    invariant forall x :: a <= x < k ==> X[x] > p
    invariant multiset(X[..]) == multiset(old(X[..]))
  {
    if X[k] <= p {
      X[a], X[k] := X[k], X[a];
      a := a + 1;
    }
    k := k + 1;
  }
  
  b := n;
}
// </vc-code>

