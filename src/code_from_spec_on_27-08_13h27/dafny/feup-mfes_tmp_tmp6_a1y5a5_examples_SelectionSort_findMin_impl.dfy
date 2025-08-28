/* 
* Formal verification of the selection sort algorithm with Dafny.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j] 
}

// Sorts array 'a' using the selection sort algorithm.

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)

// <vc-helpers>
// Helper lemma to ensure the minimum value property holds when comparing elements
lemma MinProperty(a: array<real>, from: nat, to: nat, minIdx: nat)
  requires 0 <= from < to <= a.Length
  requires from <= minIdx < to
  requires forall k :: from <= k < to ==> a[k] >= a[minIdx]
  ensures forall k :: from <= k < to ==> a[k] >= a[minIdx]
{
  // Trivial, as the property is directly in the requires clause
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
  requires 0 <= from < to <= a.Length
  ensures from <= index < to
  ensures forall k :: from <= k < to ==> a[k] >= a[index]
// </vc-spec>
// </vc-spec>

// <vc-code>
method findMin(a: array<real>, from: nat, to: nat) returns (index: nat)
  requires 0 <= from < to <= a.Length
  ensures from <= index < to
  ensures forall k :: from <= k < to ==> a[k] >= a[index]
{
  index := from;
  var i := from + 1;
  while i < to
    decreases to - i
    invariant from <= index < to
    invariant from <= i <= to
    invariant forall k :: from <= k < i ==> a[k] >= a[index]
  {
    if a[i] < a[index]
    {
      index := i;
    }
    i := i + 1;
  }
}
// </vc-code>
