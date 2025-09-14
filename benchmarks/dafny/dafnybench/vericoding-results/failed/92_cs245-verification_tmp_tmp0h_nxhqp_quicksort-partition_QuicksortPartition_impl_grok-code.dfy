// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...

/* The annotations and implied proofs are left for you.
   I might do them later on next week. */

// <vc-helpers>
method QuicksortPartition(X: array<int>, n: int, p: int) returns (a: int, b: int)
modifies X
/*Pre-Condition*/   requires X.Length>=1 && n == X.Length;
/*Post-Condition*/  ensures b>=n;
                    ensures forall x:: 0<=x<a<n ==> X[x] <= p;
                    ensures forall x:: a==n || (0<=a<=x<n ==> X[x] > p);
                    ensures multiset(X[..])==multiset(old(X[..]))           //This says the new X is a permutation of our old version of X.
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
  var i := 0;
  var j := 0;
  while i < n
    invariant 0 <= j <= i <= n
    invariant multiset(X[..]) == multiset(old(X[..]))
    invariant forall k :: 0 <= k < j ==> X[k] <= p
    invariant forall k :: j <= k < i ==> X[k] > p
  {
    if X[i] <= p {
      X[j], X[i] := X[i], X[j];
      j := j + 1;
    }
    i := i + 1;
  }
  a := j;
  b := n;
}
// </vc-code>

