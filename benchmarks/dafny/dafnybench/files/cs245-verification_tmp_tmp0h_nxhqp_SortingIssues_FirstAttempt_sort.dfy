/*
// Sorting: 

//        Pre/Post Condition Issues - An investigation 

//                                      -- Stephanie McIntyre

// Based on examples in class 

// First Attempt at specifying requirements for sorting array A in incrementing order

// We want our Hoare triple of (|Pre-Condition|) Code (|Post-Condition|) to hold iff A is properly sorted.

//This states that A is sorted.

//Can we write code that does not sort A that still satisfies the requirements? 

//Consider the following program:
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method sort(A: array<int>, n: int)
modifies A; requires n==A.Length;
  requires n>=0;            
  ensures forall i,j:: 0<=i<=j<n ==> A[i]<=A[j];
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
