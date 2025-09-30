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
// Lemma to prove that swapping preserves multiset equality
lemma SwapMultiset(a: seq<real>, i: int, j: int)
  requires 0 <= i < |a|
  requires 0 <= j < |a|
  ensures multiset(a[i := a[j]][j := a[i]]) == multiset(a)
{
  var a' := a[i := a[j]][j := a[i]];
  assert a'[i] == a[j] && a'[j] == a[i];
  
  if i == j {
    assert a' == a;
  } else {
    // All elements except at positions i and j remain the same
    assert forall k :: 0 <= k < |a| && k != i && k != j ==> a'[k] == a[k];
  }
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
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant forall j, k :: 0 <= j < i <= k < a.Length ==> a[j] <= a[k]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    if i < a.Length {
      var minIndex := findMin(a, i, a.Length);
      
      // Store old values for ghost reasoning
      ghost var oldA := a[..];
      
      // Swap a[i] with a[minIndex]
      var temp := a[i];
      a[i] := a[minIndex];
      a[minIndex] := temp;
      
      // Prove multiset preservation
      assert a[..] == oldA[i := oldA[minIndex]][minIndex := oldA[i]];
      SwapMultiset(oldA, i, minIndex);
      assert multiset(a[..]) == multiset(oldA);
      
      // Prove that sorted property is maintained
      assert a[i] == oldA[minIndex];
      assert forall k :: i < k < a.Length ==> a[i] <= a[k] by {
        assert forall k :: i < k < a.Length ==> oldA[minIndex] <= oldA[k];
      }
      
      // Elements before i are still sorted and <= elements from i onwards
      assert isSorted(a, 0, i);
      assert forall j, k :: 0 <= j < i < k < a.Length ==> a[j] <= a[k];
    }
    
    i := i + 1;
  }
  
  // The loop invariants directly establish the postcondition
  assert isSorted(a, 0, i);
  assert i == a.Length;
  assert isSorted(a, 0, a.Length);
}
// </vc-code>

