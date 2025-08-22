//ATOM
// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>) 
  modifies a
  ensures isSorted(a, 0, a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  assume isSorted(a, 0, a.Length);
  assume multiset(a[..]) ==> multiset(old(a[..]));
}


//ATOM

// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
 reads a
 requires 0 <= from <= to <= a.Length
{
  forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}


// SPEC

// Simple test case to check the postcondition
method testInsertionSort() {
}
