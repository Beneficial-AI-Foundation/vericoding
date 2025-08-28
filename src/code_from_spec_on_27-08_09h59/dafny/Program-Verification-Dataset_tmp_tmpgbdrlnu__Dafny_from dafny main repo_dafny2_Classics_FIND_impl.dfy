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
lemma PartitionProperty(A: array<int>, pivot: int, i: int, j: int)
  requires 0 <= i <= j < A.Length
  requires 0 <= pivot < A.Length
  requires forall p :: i <= p <= pivot ==> A[p] <= A[pivot]
  requires forall q :: pivot <= q <= j ==> A[pivot] <= A[q]
  ensures forall p, q :: i <= p <= pivot <= q <= j ==> A[p] <= A[q]
{
}

predicate Partitioned(A: array<int>, pivot: int, lo: int, hi: int)
  reads A
  requires 0 <= lo <= hi < A.Length
  requires 0 <= pivot < A.Length
{
  lo <= pivot <= hi &&
  (forall p :: lo <= p <= pivot ==> A[p] <= A[pivot]) &&
  (forall q :: pivot <= q <= hi ==> A[pivot] <= A[q])
}

lemma PartitionComplete(A: array<int>, f: int, N: int)
  requires 0 <= f < N == A.Length
  requires forall p :: 0 <= p <= f ==> A[p] <= A[f]
  requires forall q :: f <= q < N ==> A[f] <= A[q]
  ensures forall p, q :: 0 <= p <= f <= q < N ==> A[p] <= A[q]
{
  forall p, q | 0 <= p <= f <= q < N
    ensures A[p] <= A[q]
  {
    if p <= f && f <= q {
      assert A[p] <= A[f] <= A[q];
    }
  }
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
{
  var i := 0;
  var j := N - 1;
  var pivot := f;
  
  while i < j
    invariant 0 <= i <= j < N
    invariant 0 <= pivot < N
    invariant i <= pivot <= j
    invariant forall p :: 0 <= p < i ==> A[p] <= A[pivot]
    invariant forall q :: j < q < N ==> A[pivot] <= A[q]
    invariant forall p :: i <= p < pivot ==> A[p] <= A[pivot]
    invariant forall q :: pivot < q <= j ==> A[pivot] <= A[q]
    invariant A[pivot] <= A[pivot]
  {
    while i < pivot && A[i] <= A[pivot]
      invariant 0 <= i <= pivot
      invariant forall p :: 0 <= p < i ==> A[p] <= A[pivot]
      invariant forall p :: i <= p < pivot ==> A[p] <= A[pivot]
    {
      i := i + 1;
    }
    
    while pivot < j && A[pivot] <= A[j]
      invariant pivot <= j < N
      invariant forall q :: j < q < N ==> A[pivot] <= A[q]
      invariant forall q :: pivot < q <= j ==> A[pivot] <= A[q]
    {
      j := j - 1;
    }
    
    if i < j {
      if i == pivot {
        A[pivot], A[j] := A[j], A[pivot];
        pivot := j;
        j := j - 1;
      } else if j == pivot {
        A[i], A[pivot] := A[pivot], A[i];
        pivot := i;
        i := i + 1;
      } else {
        A[i], A[j] := A[j], A[i];
        i := i + 1;
        j := j - 1;
      }
    }
  }
  
  assert i == j;
  assert i == pivot;
  assert forall p :: 0 <= p <= f ==> A[p] <= A[f];
  assert forall q :: f <= q < N ==> A[f] <= A[q];
  PartitionComplete(A, f, N);
}
// </vc-code>
