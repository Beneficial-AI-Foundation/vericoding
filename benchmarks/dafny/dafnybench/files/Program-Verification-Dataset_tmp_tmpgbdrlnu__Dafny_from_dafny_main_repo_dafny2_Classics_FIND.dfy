/*
// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false

// A version of Turing's additive factorial program [Dr. A. Turing, "Checking a large routine",

// In "Report of a Conference of High Speed Automatic Calculating Machines", pp. 67-69, 1949].

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
*/

ghost function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
