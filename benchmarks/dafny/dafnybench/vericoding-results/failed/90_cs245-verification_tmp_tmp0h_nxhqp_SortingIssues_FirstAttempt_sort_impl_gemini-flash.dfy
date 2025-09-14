// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 

// First Attempt at specifying requirements for sorting array A in incrementing order
// We want our Hoare triple of (|Pre-Condition|) Code (|Post-Condition|) to hold iff A is properly sorted.

// <vc-helpers>
/**
 * This is an empty section for `vc-helpers`.
 * No helper functions or predicates are needed for this fix.
 */
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
  if n == 0 {
    return;
  }
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant forall x, y :: 0 <= x < y < i ==> A[x] <= A[y]
    invariant forall x :: 0 <= x < i ==> (forall y :: x < y < n ==> A[x] <= A[y]) // This ensures that A[x] is the minimum in A[x..n-1] for all x < i
    modifies A
  {
    var minIndex := i;
    for j := i + 1 to n - 1
      invariant i < j <= n
      invariant forall x, y :: 0 <= x < y < i ==> A[x] <= A[y]
      invariant i <= minIndex < j
      invariant (forall k :: i <= k < j ==> A[minIndex] <= A[k])
      modifies A
    {
      if A[j] < A[minIndex] {
        minIndex := j;
      }
    }
    if minIndex != i {
      var temp := A[i];
      A[i] := A[minIndex];
      A[minIndex] := temp;
    }
  }
}
// </vc-code>

