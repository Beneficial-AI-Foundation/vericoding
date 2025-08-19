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
  /* code modified by LLM (iteration 4): Store original array for multiset preservation */
  ghost var original_multiset := multiset(a[..]);
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant sorted_seg(a, 0, i-1)
    /* code modified by LLM (iteration 4): Use stored original multiset instead of old() */
    invariant multiset(a[..]) == original_multiset
  {
    var key := a[i];
    var j := i - 1;
    
    /* code modified by LLM (iteration 4): Store array state before inner loop for multiset tracking */
    ghost var a_before_inner := a[..];
    
    while j >= 0 && a[j] > key
      invariant -1 <= j <= i - 1
      /* code modified by LLM (iteration 4): Use stored value instead of old() */
      invariant key == a_before_inner[i]
      invariant sorted_seg(a, 0, j)
      invariant sorted_seg(a, j+2, i)
      invariant forall k :: j+2 <= k <= i ==> a[k] >= key
      /* code modified by LLM (iteration 4): Track elements that have been shifted */
      invariant forall k :: j+2 <= k <= i ==> (k < i ==> a[k] == a_before_inner[k-1])
      /* code modified by LLM (iteration 4): Multiset preservation within inner loop */
      invariant multiset(a[..]) == multiset(a_before_inner)
      /* code modified by LLM (iteration 4): Ordering between sorted segments */
      invariant forall k1, k2 :: 0 <= k1 <= j && j+2 <= k2 <= i ==> a[k1] <= a[k2]
      /* code modified by LLM (iteration 4): Key placement invariant */
      invariant j+1 < i ==> a[j+1] >= key
    {
      /* code modified by LLM (iteration 4): Add assertion to help with multiset reasoning */
      assert a[j+1] == a[j] || a[j+1] == key;
      a[j+1] := a[j];
      j := j - 1;
    }
    
    a[j+1] := key;
    
    /* code modified by LLM (iteration 4): Add lemma call to help prove multiset preservation */
    assert a[j+1] == key;
    assert forall k :: 0 <= k < a.Length && k != j+1 ==> a[k] == a_before_inner[k] || (k > j+1 && k <= i && a[k] == a_before_inner[k-1]);
    /* code modified by LLM (iteration 4): Help Dafny understand multiset equality */
    ghost var final_multiset := multiset(a[..]);
    assert final_multiset == multiset(a_before_inner);
    assert multiset(a_before_inner) == original_multiset;
    assert sorted_seg(a, 0, i);
    
    i := i + 1;
  }
}