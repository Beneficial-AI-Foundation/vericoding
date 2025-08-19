//ATOM
// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>) 
  modifies a
  ensures isSorted(a, 0, a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  /* code modified by LLM (iteration 4): Fixed loop invariants and added necessary assertions */
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var key := a[i];
    var j := i - 1;
    
    /* code modified by LLM (iteration 4): Fixed inner loop invariants to properly handle sorted segments */
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant isSorted(a, 0, j + 1)
      invariant isSorted(a, j + 2, i + 1)
      invariant forall k :: j + 2 <= k <= i ==> a[k] > key
      invariant forall k :: 0 <= k <= j ==> a[k] <= key || k == j
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    
    /* code modified by LLM (iteration 4): Added assertion to help verification */
    assert j == -1 || a[j] <= key;
    a[j + 1] := key;
    
    /* code modified by LLM (iteration 4): Added assertion to establish sortedness after insertion */
    assert isSorted(a, 0, i + 1);
    i := i + 1;
  }
}

//ATOM
// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
 reads a
 requires 0 <= from <= to <= a.Length
{
  forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

//IMPL testInsertionSort
// Simple test case to check the postcondition
method testInsertionSort() {
  /* code modified by LLM (iteration 4): Implemented comprehensive test case */
  var a := new int[3];
  a[0] := 3;
  a[1] := 1;
  a[2] := 2;
  
  var oldContents := a[..];
  insertionSort(a);
  
  /* code modified by LLM (iteration 4): Added explicit checks for test verification */
  assert a[0] <= a[1] <= a[2]; // Explicit sortedness check
  assert isSorted(a, 0, a.Length);
  assert multiset(a[..]) == multiset(oldContents);
}