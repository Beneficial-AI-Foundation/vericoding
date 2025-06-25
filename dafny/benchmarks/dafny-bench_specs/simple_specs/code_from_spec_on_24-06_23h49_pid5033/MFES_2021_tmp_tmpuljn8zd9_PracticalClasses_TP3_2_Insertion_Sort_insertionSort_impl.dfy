//ATOM

// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
 reads a
 requires 0 <= from <= to <= a.Length
{
  forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}


//IMPL 
// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>) 
  modifies a
  ensures isSorted(a, 0, a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  if a.Length <= 1 {
    return;
  }
  
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var key := a[i];
    var j := i - 1;
    
    /* code modified by LLM (iteration 1): Simplified inner loop invariants to focus on essential properties */
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[k+1] || k == j
      invariant forall k :: j + 2 <= k <= i ==> a[k] >= key
      invariant isSorted(a, 0, j + 1)
      invariant isSorted(a, j + 2, i + 1)
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    
    a[j + 1] := key;
    
    /* code modified by LLM (iteration 1): Added assertions to help prove sortedness after key insertion */
    assert forall k :: 0 <= k <= j ==> a[k] <= key;
    assert forall k :: j + 2 <= k <= i ==> key <= a[k];
    
    i := i + 1;
  }
}