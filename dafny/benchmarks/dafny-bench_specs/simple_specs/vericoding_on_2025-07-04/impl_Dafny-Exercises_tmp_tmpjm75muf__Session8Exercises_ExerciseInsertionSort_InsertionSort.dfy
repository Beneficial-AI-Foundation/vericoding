//ATOM

predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
  forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

//IMPL 

method InsertionSort(a: array<int>)
 modifies a
 ensures sorted_seg(a,0,a.Length-1) 
 ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
{
  if a.Length <= 1 {
    return;
  }
  
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant sorted_seg(a, 0, i-1)
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var key := a[i];
    var j := i - 1;
    
    /* code modified by LLM (iteration 3): Track original multiset and key position */
    ghost var original_multiset := multiset(a[..]);
    
    while j >= 0 && a[j] > key
      invariant -1 <= j <= i - 1
      /* code modified by LLM (iteration 3): Fixed sorted segment invariants */
      invariant j >= 0 ==> sorted_seg(a, 0, j)
      invariant sorted_seg(a, j+2, i)
      /* code modified by LLM (iteration 3): Elements from j+2 to i are all > key */
      invariant forall k :: j+2 <= k <= i ==> a[k] > key
      /* code modified by LLM (iteration 3): Key is stored at position i */
      invariant a[i] == key
      /* code modified by LLM (iteration 3): Multiset is preserved with key at end */
      invariant multiset(a[..]) == original_multiset
      /* code modified by LLM (iteration 3): Elements 0..j are <= elements j+2..i when j >= 0 */
      invariant j >= 0 && j+2 <= i ==> forall x, y :: 0 <= x <= j && j+2 <= y <= i ==> a[x] <= a[y]
    {
      a[j+1] := a[j];
      j := j - 1;
    }
    
    a[j+1] := key;
    
    /* code modified by LLM (iteration 3): Assert key properties after insertion */
    assert j+1 <= i;
    assert a[j+1] == key;
    assert forall k :: 0 <= k <= j ==> a[k] <= key;
    assert forall k :: j+2 <= k <= i ==> a[k] >= key;
    
    i := i + 1;
  }
}