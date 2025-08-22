/* 
* Formal verification of the selection sort algorithm with Dafny.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
//ATOM 

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j] 
}

//IMPL selectionSort

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
  modifies a
  ensures isSorted(a, 0, a.Length) 
  ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant isSorted(a, 0, i)
        invariant forall k, l :: 0 <= k < i <= l < a.Length ==> a[k] <= a[l]
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var minIndex := findMin(a, i, a.Length);
        a[i], a[minIndex] := a[minIndex], a[i];
        i := i + 1;
    }
}

//IMPL findMin

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
  requires 0 <= from < to <= a.Length
  ensures from <= index < to
  ensures forall k :: from <= k < to ==> a[k] >= a[index]
{
    index := from;
    var i := from + 1;
    while i < to
        invariant from <= index < to
        invariant from < i <= to
        invariant forall k :: from <= k < i ==> a[k] >= a[index]
    {
        if a[i] < a[index] {
            index := i;
        }
        i := i + 1;
    }
}

//ATOM_PLACEHOLDER_testSelectionSort

//ATOM_PLACEHOLDER_testFindMin