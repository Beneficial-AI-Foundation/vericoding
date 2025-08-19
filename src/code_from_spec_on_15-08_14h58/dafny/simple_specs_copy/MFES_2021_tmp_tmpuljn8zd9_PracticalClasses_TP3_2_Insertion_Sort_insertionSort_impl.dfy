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
  /* code modified by LLM (iteration 4): Complete rewrite with correct invariants */
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
    
    /* code modified by LLM (iteration 4): Capture array state at start of outer loop iteration */
    ghost var a_before_inner := a[..];
    
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant key == a_before_inner[i]
      /* code modified by LLM (iteration 4): Elements after j+1 are shifted from their positions at loop start */
      invariant forall k :: j + 2 <= k <= i ==> a[k] == a_before_inner[k - 1]
      /* code modified by LLM (iteration 4): Elements before and after affected region unchanged */
      invariant forall k :: 0 <= k <= j ==> a[k] == a_before_inner[k]
      invariant forall k :: i + 1 <= k < a.Length ==> a[k] == a_before_inner[k]
      /* code modified by LLM (iteration 4): Maintain sortedness of unaffected regions */
      invariant isSorted(a, 0, j + 1)
      invariant j + 2 <= i ==> isSorted(a, j + 2, i + 1)
      /* code modified by LLM (iteration 4): Elements in shifted region are greater than key */
      invariant forall k :: j + 1 < k <= i ==> a[k] > key
      /* code modified by LLM (iteration 4): Multiset preserved relative to start of outer iteration */
      invariant multiset(a[..]) == multiset(a_before_inner[..])
      decreases j
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    
    a[j + 1] := key;
    
    /* code modified by LLM (iteration 4): Assert sortedness properties to help verification */
    assert forall k :: 0 <= k <= j ==> a[k] <= key;
    assert forall k :: j + 2 <= k <= i ==> key <= a[k];
    assert isSorted(a, 0, i + 1);
    
    i := i + 1;
  }
}