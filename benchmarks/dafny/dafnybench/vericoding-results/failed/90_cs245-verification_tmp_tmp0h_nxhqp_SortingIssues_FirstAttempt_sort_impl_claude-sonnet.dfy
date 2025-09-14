// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 

// First Attempt at specifying requirements for sorting array A in incrementing order
// We want our Hoare triple of (|Pre-Condition|) Code (|Post-Condition|) to hold iff A is properly sorted.

// <vc-helpers>
lemma SortedArrayProperty(A: array<int>, n: int)
  requires n == A.Length
  requires n >= 0
  requires forall i,j:: 0<=i<=j<n ==> A[i]<=A[j]
  ensures forall k:: 0 <= k < n-1 ==> A[k] <= A[k+1]
{
}

lemma SingleElementSorted(A: array<int>)
  requires A.Length <= 1
  ensures forall i,j:: 0<=i<=j<A.Length ==> A[i]<=A[j]
{
}

lemma BubbleProperty(A: array<int>, start: int, end: int)
  requires 0 <= start < end < A.Length
  requires forall k:: start <= k < end ==> A[k] <= A[end]
  ensures A[start] <= A[end]
{
}

lemma BubbleInvariantPreservation(A: array<int>, i: int, j: int, n: int)
  requires 0 <= i < n - 1
  requires 0 <= j < n - 1 - i
  requires n == A.Length
  requires forall x,y:: 0 <= x <= y < i ==> A[x] <= A[y]
  requires forall x:: 0 <= x < i ==> forall y:: i <= y < n ==> A[x] <= A[y]
  requires forall x:: i <= x < i + j && i + j < n ==> A[x] <= A[i + j]
  requires i + j + 1 < n && A[i + j] <= A[i + j + 1]
  ensures forall x:: i <= x < i + j + 1 && i + j + 1 < n ==> A[x] <= A[i + j + 1]
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
  if n <= 1 {
    return;
  }
  
  // Simple bubble sort implementation
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant forall x,y:: 0 <= x <= y < i ==> A[x] <= A[y]
    invariant forall x:: 0 <= x < i ==> forall y:: i <= y < n ==> A[x] <= A[y]
  {
    var j := 0;
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant forall x,y:: 0 <= x <= y < i ==> A[x] <= A[y]
      invariant forall x:: 0 <= x < i ==> forall y:: i <= y < n ==> A[x] <= A[y]
      invariant forall x:: i <= x < i + j ==> A[x] <= A[n - 1 - i]
      invariant forall x:: i <= x < i + j && x + 1 < n ==> A[x] <= A[x + 1]
    {
      if A[i + j] > A[i + j + 1] {
        var temp := A[i + j];
        A[i + j] := A[i + j + 1];
        A[i + j + 1] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

