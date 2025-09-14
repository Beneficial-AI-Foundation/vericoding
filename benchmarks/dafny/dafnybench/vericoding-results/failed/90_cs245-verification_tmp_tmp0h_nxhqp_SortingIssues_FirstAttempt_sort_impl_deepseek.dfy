// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 

// First Attempt at specifying requirements for sorting array A in incrementing order
// We want our Hoare triple of (|Pre-Condition|) Code (|Post-Condition|) to hold iff A is properly sorted.

// <vc-helpers>
predicate sorted(A: array<int>, n: int)
  requires n >= 0
  requires n <= A.Length
  reads A
{
  forall i,j :: 0 <= i <= j < n ==> A[i] <= A[j]
}

lemma sorted_implies_monotonic(A: array<int>, n: int)
  requires n >= 0 && n <= A.Length
  requires sorted(A, n)
  ensures forall i,j :: 0 <= i <= j < n ==> A[i] <= A[j]
{
}

lemma monotonic_implies_sorted(A: array<int>, n: int)
  requires n >= 0 && n <= A.Length
  requires forall i,j :: 0 <= i <= j < n ==> A[i] <= A[j]
  ensures sorted(A, n)
{
}

lemma swap_preserves_outer_elements(A: array<int>, i: int, j: int, n: int)
  requires 0 <= i < j < n
  modifies A
  ensures forall k :: 0 <= k < n && k != i && k != j ==> A[k] == old(A[k])
{
}

lemma partition_invariant(A: array<int>, n: int, i: int, min_index: int)
  requires 0 <= i < n
  requires i <= min_index < n
  requires forall k :: i <= k < n ==> A[min_index] <= A[k]
  ensures forall p, q :: 0 <= p <= q < i ==> A[p] <= A[q]
  ensures forall p, q :: 0 <= p < i && i <= q < n ==> A[p] <= A[q]
{
}
// </vc-helpers>

// <vc-spec>
method sort(A: array<int>, n: int)
modifies A; requires n==A.Length;
/* Pre-Condition */   requires n>=0;            
/* Post-Condition */  ensures forall i,j:: 0<=i<=j<n ==> A[i]<=A[j];  //This states that A is sorted.

//Can we write code that does not sort A that still satisfies the requirements? 
//Consider the following program:
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall p, q :: 0 <= p <= q < i ==> A[p] <= A[q]
    invariant forall p, q :: 0 <= p < i && i <= q < n ==> A[p] <= A[q]
  {
    var min_index := i;
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant i <= min_index < n
      invariant forall k :: i <= k < j ==> A[min_index] <= A[k]
    {
      if A[j] < A[min_index] {
        min_index := j;
      }
      j := j + 1;
    }
    if min_index != i {
      var temp := A[i];
      A[i] := A[min_index];
      A[min_index] := temp;
    }
    // partition_invariant(A, n, i, min_index);
    i := i + 1;
  }
}
// </vc-code>

