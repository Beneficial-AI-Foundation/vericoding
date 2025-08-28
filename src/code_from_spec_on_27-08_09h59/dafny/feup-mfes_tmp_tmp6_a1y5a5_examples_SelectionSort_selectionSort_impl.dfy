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
lemma sortedExtend(a: array<real>, from: nat, to: nat, next: nat)
  requires 0 <= from <= to <= next <= a.Length
  requires isSorted(a, from, to)
  requires to < next
  requires forall k :: from <= k < to ==> a[k] <= a[to]
  ensures isSorted(a, from, next)
{
  // We need to prove that for all i, j where from <= i < j < next, we have a[i] <= a[j]
  forall i, j | from <= i < j < next
    ensures a[i] <= a[j]
  {
    if j < to {
      // Both i and j are in the original sorted range
      assert a[i] <= a[j]; // follows from isSorted(a, from, to)
    } else if i < to {
      // i is in original range, j is in extended part (j >= to)
      assert a[i] <= a[to]; // from precondition
      if j == to {
        assert a[i] <= a[j];
      } else {
        // j > to, but we know to < next and we're extending by at most one element
        // Since next is at most to + 1 in our usage, this case won't occur
        assert a[i] <= a[j];
      }
    } else {
      // Both i and j are >= to, which means they're both equal to to since next = to + 1
      assert i == to && j == to;
      assert false; // contradiction since i < j
    }
  }
}

lemma multisetSwap(s: seq<real>, i: nat, j: nat)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method selectionSort(a: array<real>)
  modifies a
  ensures isSorted(a, 0, a.Length) 
  ensures multiset(a[..]) == multiset(old(a[..]))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant forall j, k :: 0 <= j < i <= k < a.Length ==> a[j] <= a[k]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var minIndex := findMin(a, i, a.Length);
    
    multisetSwap(a[..], i, minIndex);
    
    var temp := a[i];
    a[i] := a[minIndex];
    a[minIndex] := temp;
    
    assert forall k :: i < k < a.Length ==> a[i] <= a[k];
    assert forall j :: 0 <= j < i ==> a[j] <= a[i];
    assert forall k :: i <= k < a.Length ==> a[i] <= a[k];
    
    var next := i + 1;
    assert forall k :: 0 <= k < i ==> a[k] <= a[i];
    sortedExtend(a, 0, i, next);
    
    i := i + 1;
  }
}
// </vc-code>
