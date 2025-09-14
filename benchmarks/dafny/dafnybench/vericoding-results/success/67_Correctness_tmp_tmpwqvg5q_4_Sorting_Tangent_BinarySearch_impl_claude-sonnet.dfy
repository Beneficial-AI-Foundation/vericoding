/**
  Ather, Mohammad Faiz (s4648481/3)
  CSSE3100
  Assignemnt 3
  The University of Queensland
 */

// Question 1

// Author: Leino, Title: Program Proofs

// <vc-helpers>
lemma ArrayStrictlyIncreasing(a: array<int>, i: int, j: int)
  requires forall k :: 1 <= k < a.Length ==> a[k-1] < a[k]
  requires 0 <= i < j < a.Length
  ensures a[i] < a[j]
{
  if i + 1 == j {
    // Base case: adjacent elements
  } else {
    // Inductive case
    ArrayStrictlyIncreasing(a, i, j-1);
    assert a[i] < a[j-1];
    assert a[j-1] < a[j];
  }
}
// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array<int>, circle: int)
  returns (n: int)
  requires forall i ::
           1 <= i < a.Length
           ==> a[i-1] < a[i]
  requires forall i, j ::
           0 <= i < j < a.Length ==>
           a[i] < a[j]
  ensures 0 <= n <= a.Length
  ensures forall i ::
          0 <= i < n ==>
          a[i] < circle
  ensures forall i ::
          n <= i < a.Length ==>
          circle <= a[i]
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := a.Length;
  
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < low ==> a[i] < circle
    invariant forall i :: high <= i < a.Length ==> circle <= a[i]
    decreases high - low
  {
    var mid := (low + high) / 2;
    
    if a[mid] < circle {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  n := low;
}
// </vc-code>

