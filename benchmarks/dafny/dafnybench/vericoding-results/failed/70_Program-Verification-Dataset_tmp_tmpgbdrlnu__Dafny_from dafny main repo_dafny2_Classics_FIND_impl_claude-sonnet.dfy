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
ghost predicate Partitioned(A: array<int>, N: int, f: int, i: int, j: int)
  reads A
  requires 0 <= i <= f < A.Length
  requires 0 <= j < A.Length
{
  forall p :: i <= p <= f ==> A[p] <= A[f]
}

ghost predicate PartitionedRight(A: array<int>, N: int, f: int, i: int, j: int)
  reads A
  requires 0 <= f <= j < A.Length
  requires 0 <= i < A.Length
{
  forall q :: f <= q <= j ==> A[f] <= A[q]
}

lemma PartitionPreservation(A: array<int>, N: int, f: int, i: int, j: int, old_i: int, old_j: int)
  requires 0 <= old_i <= i <= f <= j <= old_j < N
  requires f < A.Length
  requires Partitioned(A, N, f, old_i, i-1)
  requires PartitionedRight(A, N, f, j+1, old_j)
  ensures forall p :: old_i <= p < i ==> A[p] <= A[f]
  ensures forall q :: j < q <= old_j ==> A[f] <= A[q]
{
}

lemma PostconditionLemma(A: array<int>, N: int, f: int, pivot: int)
  requires 0 <= f < N == A.Length
  requires 0 <= pivot < N
  requires forall p :: 0 <= p < N && p <= pivot ==> A[p] <= A[pivot]
  requires forall q :: 0 <= q < N && pivot <= q ==> A[pivot] <= A[q]
  ensures forall p, q :: 0 <= p <= f <= q < N ==> A[p] <= A[q]
{
  forall p, q | 0 <= p <= f <= q < N
    ensures A[p] <= A[q]
  {
    if p <= pivot <= q {
      assert A[p] <= A[pivot] <= A[q];
    } else if f <= pivot {
      assert A[p] <= A[f] <= A[pivot] <= A[q];
    } else {
      assert A[p] <= A[pivot] <= A[f] <= A[q];
    }
  }
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
  var i, j := 0, N - 1;
  var pivot := f;
  
  while i < pivot || pivot < j
    invariant 0 <= i <= pivot <= j < N
    invariant forall p :: 0 <= p < i ==> A[p] <= A[pivot]
    invariant forall q :: j < q < N ==> A[pivot] <= A[q]
    invariant forall p :: 0 <= p <= pivot ==> A[p] <= A[pivot]
    invariant forall q :: pivot <= q < N ==> A[pivot] <= A[q]
    decreases (pivot - i) + (j - pivot)
  {
    while i < pivot && A[i] <= A[pivot]
      invariant 0 <= i <= pivot <= j < N
      invariant forall p :: 0 <= p < i ==> A[p] <= A[pivot]
      invariant forall q :: j < q < N ==> A[pivot] <= A[q]
      invariant forall p :: 0 <= p <= pivot ==> A[p] <= A[pivot]
      invariant forall q :: pivot <= q < N ==> A[pivot] <= A[q]
    {
      i := i + 1;
    }
    
    while pivot < j && A[pivot] <= A[j]
      invariant 0 <= i <= pivot <= j < N
      invariant forall p :: 0 <= p < i ==> A[p] <= A[pivot]
      invariant forall q :: j < q < N ==> A[pivot] <= A[q]
      invariant forall p :: 0 <= p <= pivot ==> A[p] <= A[pivot]
      invariant forall q :: pivot <= q < N ==> A[pivot] <= A[q]
    {
      j := j - 1;
    }
    
    if i < pivot && pivot < j {
      A[i], A[j] := A[j], A[i];
      i, j := i + 1, j - 1;
    } else if i < pivot {
      A[i], A[pivot] := A[pivot], A[i];
      pivot := i;
    } else if pivot < j {
      A[pivot], A[j] := A[j], A[pivot];
      pivot := j;
    }
  }
  
  PostconditionLemma(A, N, f, pivot);
}
// </vc-code>

