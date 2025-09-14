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
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
  requires 0 <= from < to <= a.Length
  ensures from <= index < to
  ensures forall k :: from <= k < to ==> a[k] >= a[index]
{
  assume{:axiom} false;
}

// <vc-helpers>
method swap(a: array<real>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var tmp := a[i];
  a[i] := a[j];
  a[j] := tmp;
}
// </vc-helpers>

// <vc-spec>
method selectionSort(a: array<real>)
  modifies a
  ensures isSorted(a, 0, a.Length) 
  ensures multiset(a[..]) == multiset(old(a[..]))
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  ghost var orig := a[..];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant isSorted(a, 0, i)
    invariant forall p, q :: 0 <= p < i <= q < n ==> a[p] <= a[q]
    invariant multiset(a[..]) == multiset(orig)
  {
    var min := i;
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant i <= min < n
      invariant forall k :: i <= k < j ==> a[min] <= a[k]
    {
      if a[j] < a[min] {
        min := j;
      }
      j := j + 1;
    }
    if i != min {
      // inline swap so verifier can relate values directly
      var tmp := a[i];
      a[i] := a[min];
      a[min] := tmp;
    }
    i := i + 1;
  }
}
// </vc-code>

