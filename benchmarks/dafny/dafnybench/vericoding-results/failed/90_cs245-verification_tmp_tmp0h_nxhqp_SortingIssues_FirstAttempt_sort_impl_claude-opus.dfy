// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 

// First Attempt at specifying requirements for sorting array A in incrementing order
// We want our Hoare triple of (|Pre-Condition|) Code (|Post-Condition|) to hold iff A is properly sorted.

// <vc-helpers>

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
    invariant forall j, k :: 0 <= j <= k < i ==> A[j] <= A[k]
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < n ==> A[j] <= A[k]
  {
    var minIndex := i;
    var j := i + 1;
    while j < n
      invariant i < j <= n
      invariant i <= minIndex < n
      invariant forall k :: i <= k < j ==> A[minIndex] <= A[k]
    {
      if A[j] < A[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      var temp := A[i];
      A[i] := A[minIndex];
      A[minIndex] := temp;
    }
    
    i := i + 1;
  }
}
// </vc-code>

