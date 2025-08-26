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

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method selectionSort(a: array<real>)
  modifies a
  ensures isSorted(a, 0, a.Length) 
  ensures multiset(a[..]) == multiset(old(a[..]))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant forall k1, k2 :: 0 <= k1 < i <= k2 < a.Length ==> a[k1] <= a[k2]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    if i < a.Length - 1 {
      var minIndex := findMin(a, i, a.Length);
      // Swap elements at positions i and minIndex
      var temp := a[i];
      a[i] := a[minIndex];
      a[minIndex] := temp;
    }
    i := i + 1;
  }
}
// </vc-code>

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
  requires 0 <= from < to <= a.Length
  ensures from <= index < to
  ensures forall k :: from <= k < to ==> a[k] >= a[index]
{
    var i := from + 1;
    index := from; // position of min up to position i (excluded)
    while i < to
      decreases a.Length - i
      invariant from <= index < i <= to
      invariant forall k :: from <= k < i ==> a[k] >= a[index]  
    {
        if a[i] < a[index] {
            index := i;
        }
        i := i + 1;
    }
}