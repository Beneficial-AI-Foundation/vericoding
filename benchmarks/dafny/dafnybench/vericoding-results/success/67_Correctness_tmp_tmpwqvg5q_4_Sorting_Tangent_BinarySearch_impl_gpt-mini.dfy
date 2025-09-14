/**
  Ather, Mohammad Faiz (s4648481/3)
  CSSE3100
  Assignemnt 3
  The University of Queensland
 */

// Question 1

// Author: Leino, Title: Program Proofs

// <vc-helpers>
// No helper definitions required for this verification.
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
    var mid := low + (high - low) / 2;
    assert 0 <= mid < a.Length;
    if a[mid] < circle {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  n := low;
  return;
}
// </vc-code>

