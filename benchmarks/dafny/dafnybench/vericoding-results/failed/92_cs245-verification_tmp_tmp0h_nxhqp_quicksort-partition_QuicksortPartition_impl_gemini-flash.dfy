// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...

/* The annotations and implied proofs are left for you.
   I might do them later on next week. */

// <vc-helpers>
function multiset_from_array<T>(a: array<T>): multiset<T>
  reads a
{
  multiset(a[..])
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
  var L := 0;
  var R := n - 1;

  while L <= R
    invariant 0 <= L <= n
    invariant -1 <= R < n
    invariant forall i :: 0 <= i < L ==> X[i] <= p
    invariant forall i :: R < i < n ==> X[i] > p
    invariant L <= R + 1 // Ensures partitions don't overlap or cross
    invariant multiset(X[..]) == multiset(old(X[..]))
  {
    if X[L] <= p {
      L := L + 1;
    } else if X[R] > p {
      R := R - 1;
    } else {
      // X[L] > p and X[R] <= p, so swap them
      var temp := X[L];
      X[L] := X[R];
      X[R] := temp;
      L := L + 1;
      R := R - 1;
    }
  }
  return L, L; // L is the correct value for 'a' and 'b' (partition point)
}
// </vc-code>

