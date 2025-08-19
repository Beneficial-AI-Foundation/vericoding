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
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var key := a[i];
    var j := i - 1;
    
    /* code modified by LLM (iteration 1): Fixed loop invariants to properly track array state and maintain sortedness */
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant a[i] == key
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[k+1] || k == j
      invariant forall k :: j + 2 <= k <= i ==> a[k] >= key
      invariant forall k :: i < k < a.Length ==> a[k] == old(a[..])[k]
      invariant isSorted(a, 0, j+1)
      invariant isSorted(a, j+2, i+1)
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    
    a[j + 1] := key;
    i := i + 1;
  }
}