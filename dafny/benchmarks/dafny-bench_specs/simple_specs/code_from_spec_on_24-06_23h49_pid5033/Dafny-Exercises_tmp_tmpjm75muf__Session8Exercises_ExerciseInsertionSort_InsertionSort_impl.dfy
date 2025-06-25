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
    
    /* code modified by LLM (iteration 1): Fixed invariants and added proper multiset tracking */
    ghost var pre_inner := multiset(a[..]);
    
    while j >= 0 && a[j] > key
      invariant -1 <= j <= i - 1
      invariant sorted_seg(a, 0, j) || j == -1
      invariant j < i - 1 ==> sorted_seg(a, j+2, i)
      invariant j < i - 1 ==> (forall k :: j+2 <= k <= i ==> key < a[k])
      invariant multiset(a[..]) == pre_inner
      invariant a[i] == key
      invariant j < i - 1 ==> a[j+1] == a[j+2] // Elements have been shifted right
      decreases j + 1
    {
      a[j+1] := a[j];
      j := j - 1;
    }
    
    a[j+1] := key;
    
    /* code modified by LLM (iteration 1): Added comprehensive assertions to prove sortedness */
    // After placing key at position j+1, prove the segment is sorted
    
    // Case 1: If j == -1, key is placed at position 0
    if j == -1 {
      assert a[0] == key;
      assert forall k :: 1 <= k <= i ==> key <= a[k];
      assert sorted_seg(a, 0, i);
    } else {
      // Case 2: key is placed at position j+1 where j >= 0
      assert sorted_seg(a, 0, j);
      assert a[j+1] == key;
      assert forall k :: 0 <= k <= j ==> a[k] <= key;
      assert forall k :: j+2 <= k <= i ==> key <= a[k];
      assert sorted_seg(a, j+2, i);
      
      // Prove transitivity: elements before j+1 <= key <= elements after j+1
      assert forall l, k :: 0 <= l <= j && j+2 <= k <= i ==> a[l] <= a[k];
      assert forall l :: 0 <= l <= j ==> a[l] <= a[j+1];
      assert forall k :: j+2 <= k <= i ==> a[j+1] <= a[k];
      
      // Combine all parts to show entire segment is sorted
      assert sorted_seg(a, 0, i);
    }
    
    i := i + 1;
  }
}