// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 

// First Attempt at specifying requirements for sorting array A in incrementing order
// We want our Hoare triple of (|Pre-Condition|) Code (|Post-Condition|) to hold iff A is properly sorted.

// <vc-helpers>
// No changes needed to helpers; the existing code suffices for verification.
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
  if (n < 1) {
    return;
  }
  var i := 1;
  while (i < n)
    decreases n - i;
    invariant 1 <= i <= n;
    invariant forall k,m :: 0 <= k < m < i ==> A[k] <= A[m];
  {
    var key := A[i];
    var j := i - 1;
    while (j >= 0 && A[j] > key)
      decreases j;
      invariant -1 <= j <= i-1;
      invariant forall k :: 0 <= k <= j ==> A[k] <= key;
      invariant forall k,m :: 0 <= k < m <= j ==> A[k] <= A[m];
    {
      A[j+1] := A[j];
      j := j - 1;
    }
    A[j+1] := key;
    i := i + 1;
  }
}
// </vc-code>

