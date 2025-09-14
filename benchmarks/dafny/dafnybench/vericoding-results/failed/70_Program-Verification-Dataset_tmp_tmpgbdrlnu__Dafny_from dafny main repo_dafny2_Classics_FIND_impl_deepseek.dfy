// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// A version of Turing's additive factorial program [Dr. A. Turing, "Checking a large routine",
// In "Report of a Conference of High Speed Automatic Calculating Machines", pp. 67-69, 1949].

ghost function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}


// Hoare's FIND program [C.A.R. Hoare, "Proof of a program: FIND", CACM 14(1): 39-45, 1971].
// The proof annotations here are not the same as in Hoare's article.

// In Hoare's words:
//   This program operates on an array A[1:N], and a value of f (1 <= f <= N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q (1 <= p <= f <= q <= N ==> A[p] <= A[f] <= A[q]).
//
// Here, we use 0-based indices, so we would say:
//   This method operates on an array A[0..N], and a value of f (0 <= f < N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[f] <= A[q]).

// <vc-helpers>
predicate Permutation(a: array<int>, b: array<int>)
  requires a != null && b != null
  reads a, b
{
  a.Length == b.Length &&
  multiset(a[..]) == multiset(b[..])
}

predicate SortedSegment(a: array<int>, low: int, high: int)
  requires a != null
  requires 0 <= low <= high <= a.Length
  reads a
{
  forall i, j :: low <= i <= j < high ==> a[i] <= a[j]
}

lemma PermutationPreservesLength(a: array<int>, b: array<int>)
  requires a != null && b != null
  requires Permutation(a, b)
  ensures a.Length == b.Length
{
}

lemma PermutationTransitive(a: array<int>, b: array<int>, c: array<int>)
  requires a != null && b != null && c != null
  requires Permutation(a, b) && Permutation(b, c)
  ensures Permutation(a, c)
{
}

lemma PermutationReflexive(a: array<int>)
  requires a != null
  ensures Permutation(a, a)
{
}

lemma PermutationSymmetric(a: array<int>, b: array<int>)
  requires a != null && b != null
  requires Permutation(a, b)
  ensures Permutation(b, a)
{
}

lemma SwapPreservesMultiset(a: array<int>, i: int, j: int)
  requires a != null
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures multiset(old(a[..])) == multiset(a[..])
{
  var old_a := a[..];
  a[i], a[j] := a[j], a[i];
  assert multiset(a[..]) == multiset(old_a);
}
// </vc-helpers>

// <vc-spec>
method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N;
  requires 0 <= f < N;
  modifies A;
  ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q];
// </vc-spec>
// <vc-code>
{
  var m, n : int;
  var x : int;
  m := 0;
  n := A.Length - 1;
  var tracked_f := f;
  
  while (m < n)
    invariant 0 <= m <= tracked_f <= n < A.Length
    invariant forall p :: 0 <= p < m ==> A[p] <= A[tracked_f]
    invariant forall q :: n < q < A.Length ==> A[tracked_f] <= A[q]
    decreases n - m
  {
    x := A[tracked_f];
    
    var i, j : int;
    i := m;
    j := n;
    
    while (i <= j)
      invariant m <= i <= j + 1
      invariant j >= m - 1
      invariant i <= n + 1
      invariant forall p :: 0 <= p < i ==> A[p] <= x
      invariant forall q :: j < q < A.Length ==> x <= A[q]
      invariant i <= tracked_f <= j
      decreases j - i
    {
      while (A[i] < x)
        invariant i <= tracked_f
        invariant forall p :: 0 <= p < i ==> A[p] <= x
        decreases tracked_f - i
      {
        i := i + 1;
      }
      
      while (x < A[j])
        invariant j >= tracked_f
        invariant forall q :: j < q < A.Length ==> x <= A[q]
        decreases j - tracked_f
      {
        j := j - 1;
      }
      
      if (i <= j) {
        var temp := A[i];
        A[i] := A[j];
        A[j] := temp;
        if (i == tracked_f) {
          tracked_f := j;
        } else if (j == tracked_f) {
          tracked_f := i;
        }
        i := i + 1;
        j := j - 1;
      }
    }
    
    m := i;
    n := j;
  }
}
// </vc-code>

