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
// Helper lemma to prove properties about array swaps
lemma SwapPreservesOtherElements(A: array<int>, i: int, j: int, oldA: seq<int>)
  requires 0 <= i < A.Length && 0 <= j < A.Length
  requires oldA == A[..]
  ensures forall k :: 0 <= k < A.Length && k != i && k != j ==> A[k] == oldA[k]
{
}

// Helper lemma to prove bounds are preserved after swap
lemma SwapPreservesBounds(A: array<int>, i: int, j: int, oldA: seq<int>, m: int, f: int, n: int)
  requires 0 <= i < A.Length && 0 <= j < A.Length
  requires 0 <= m <= f <= n < A.Length
  requires oldA == A[..]
  ensures forall p, q :: 0 <= p <= m <= f <= q < A.Length && p != i && p != j && q != i && q != j ==> (A[p] <= A[q]) == (oldA[p] <= oldA[q])
  ensures forall p, q :: 0 <= p <= f <= q <= n < A.Length && p != i && p != j && q != i && q != j ==> (A[p] <= A[q]) == (oldA[p] <= oldA[q])
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N;
  requires 0 <= f < N;
  modifies A;
  ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q];
// </vc-spec>
// </vc-spec>

// <vc-code>
method Find(A: array<int>, N: int, f: int)
  requires A.Length == N
  requires 0 <= f < N
  modifies A
  ensures forall p, q :: 0 <= p <= f <= q < N ==> A[p] <= A[q]
{
  var m := 0;
  var n := N - 1;
  
  while m != f || n != f
    invariant 0 <= m <= f <= n < N
    invariant forall p, q :: 0 <= p <= m && m <= f && f <= q < N ==> A[p] <= A[q]
    invariant forall p, q :: 0 <= p <= f && f <= q <= n && q < N ==> A[p] <= A[q]
    decreases n - m
  {
    if m != f {
      if A[m] > A[f] {
        var oldA := A[..];
        A[m], A[f] := A[f], A[m];
        SwapPreservesOtherElements(A, m, f, oldA);
        SwapPreservesBounds(A, m, f, oldA, m, f, n);
      }
      m := m + 1;
    } else {
      if A[f] > A[n] {
        var oldA := A[..];
        A[f], A[n] := A[n], A[f];
        SwapPreservesOtherElements(A, f, n, oldA);
        SwapPreservesBounds(A, f, n, oldA, m, f, n);
      }
      n := n - 1;
    }
  }
}
// </vc-code>
