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
// (no helpers needed)
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
  var i := 0;
  while i < N
    decreases N - i
    invariant 0 <= i <= N
    invariant forall x,y :: 0 <= x <= y < i ==> A[x] <= A[y]
    invariant forall x,y :: 0 <= x < i <= y < N ==> A[x] <= A[y]
  {
    var m := i;
    var j := i + 1;
    while j < N
      decreases N - j
      invariant i <= m < N
      invariant i + 1 <= j <= N
      invariant i <= m < j
      invariant forall k :: i <= k < j ==> A[m] <= A[k]
      invariant forall x,y :: 0 <= x <= y < i ==> A[x] <= A[y]
      invariant forall x,y :: 0 <= x < i <= y < N ==> A[x] <= A[y]
    {
      var newm := m;
      if A[j] < A[m] {
        newm := j;
      }
      j := j + 1;
      m := newm;
    }
    if m != i {
      var tmp := A[i];
      A[i] := A[m];
      A[m] := tmp;
    }
    i := i + 1;
  }
}
// </vc-code>

