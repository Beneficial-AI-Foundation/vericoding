// Sorts array 'a' using the insertion sort algorithm.
// SPEC 
// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>) 
    modifies a
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
{
}


// Checks if array 'a' is sorted.
// ATOM 

// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
  reads a
  requires 0 <= from <= to <= a.Length
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}


// Simple test case to check the postcondition
//ATOM_PLACEHOLDER_testInsertionSort



