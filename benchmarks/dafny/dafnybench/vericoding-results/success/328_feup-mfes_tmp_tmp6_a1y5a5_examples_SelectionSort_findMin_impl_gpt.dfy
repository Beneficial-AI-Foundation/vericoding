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

// </vc-helpers>

// <vc-spec>
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
  requires 0 <= from < to <= a.Length
  ensures from <= index < to
  ensures forall k :: from <= k < to ==> a[k] >= a[index]
// </vc-spec>
// <vc-code>
{
  var min: nat := from;
  var i: nat := from;
  while i < to
    invariant from <= i <= to
    invariant from <= min < to
    invariant forall k | from <= k && k < i :: a[min] <= a[k]
    decreases (to as int) - i
  {
    if a[i] < a[min] {
      min := i;
    }
    i := i + 1;
  }
  index := min;
}
// </vc-code>

