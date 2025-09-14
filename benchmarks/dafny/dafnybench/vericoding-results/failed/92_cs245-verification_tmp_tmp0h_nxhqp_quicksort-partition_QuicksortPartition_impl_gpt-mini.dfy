// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...

/* The annotations and implied proofs are left for you.
   I might do them later on next week. */

// <vc-helpers>
lemma SeqEqFromForallSeq(T: seq<int>, S: seq<int>)
  requires |T| == |S|
  requires forall i :: 0 <= i < |T| ==> T[i] == S[i]
  ensures T == S
{
  if |T| == 0 {
  } else {
    SeqEqFromForallSeq(T[1..], S[1..]);
  }
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
  var A0 := X[..];
  var L: seq<int> := [];
  var R: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |L| + |R| == i
    invariant multiset(L + R) == multiset(A0[..i])
    invariant forall k :: 0 <= k < |L| ==> L[k] <= p
    invariant forall k :: 0 <= k < |R| ==> R[k] > p
    decreases n - i
  {
    if A0[i] <= p {
      L := L + [A0[i]];
    } else {
      R := R + [A0[i]];
    }
    i := i + 1;
  }
  var S := L + R;
  assert |S| == n;
  assert multiset(S) == multiset(A0);
  a := |L|;
  assert forall k :: 0 <= k < a ==> S[k] <= p;
  assert forall k :: a <= k < n ==> S[k] > p;
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant forall k :: 0 <= k < j ==> X[k] == S[k]
    invariant forall k :: 0 <= k < a ==> S[k] <= p
    invariant forall k :: a <= k < n ==> S[k] > p
    invariant multiset(S) == multiset(A0)
    invariant |S| == n
    decreases n - j
  {
    X[j] := S[j];
    j := j + 1;
  }
  SeqEqFromForallSeq(X[..], S);
  assert forall x :: 0 <= x < a ==> X[x] <= p;
  assert a == n || forall x :: a <= x < n ==> X[x] > p;
  assert multiset(X[..]) == multiset(A0);
  b := n;
}
// </vc-code>

