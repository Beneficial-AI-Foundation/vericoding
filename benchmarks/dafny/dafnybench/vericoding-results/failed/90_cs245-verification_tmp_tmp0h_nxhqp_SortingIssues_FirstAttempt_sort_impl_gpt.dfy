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
    invariant forall a, b :: 0 <= a <= b < i ==> A[a] <= A[b]
    invariant forall k :: 0 <= k < i ==> forall m :: i <= m < n ==> A[k] <= A[m]
    decreases n - i
  {
    var m := i;
    var j := i + 1;
    while j < n
      invariant i <= m < n
      invariant i + 1 <= j <= n
      invariant forall t :: i <= t < j ==> A[m] <= A[t]
      decreases n - j
    {
      if A[j] < A[m] {
        m := j;
      }
      j := j + 1;
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

