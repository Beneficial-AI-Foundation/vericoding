predicate sorted(arr: array<int>, start: int, end: int)
requires 0 <= start <= end <= arr.Length
reads arr
{
  forall i, j :: start <= i <= j < end ==> arr[i] <= arr[j]
}

//IMPL 
method sortArray(arr: array<int>) returns (arr_sorted: array<int>)
  // Requires array length to be between 0 and 10000
  requires 0 <= arr.Length < 10000
  // Ensuring the arry has been sorted
  ensures sorted(arr_sorted, 0, arr_sorted.Length)
  // Ensuring that we have not modified elements but have only changed their indices
  ensures multiset(arr[..]) == multiset(arr_sorted[..])

  // Modifies arr
  modifies arr
{
  arr_sorted := new int[arr.Length];
  
  if arr.Length == 0 {
    return;
  }
  
  // Copy elements from original array to new array
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> arr_sorted[k] == arr[k]
    /* code modified by LLM (iteration 2): fix multiset invariant for partial array */
    invariant multiset(arr_sorted[..i]) == multiset(arr[..i])
  {
    arr_sorted[i] := arr[i];
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 2): establish multiset equality after complete copy */
  assert multiset(arr_sorted[..]) == multiset(arr[..]);
  
  // Simple insertion sort
  i := 1;
  while i < arr_sorted.Length
    invariant 1 <= i <= arr_sorted.Length
    invariant sorted(arr_sorted, 0, i)
    /* code modified by LLM (iteration 2): remove problematic multiset invariant from outer loop */
  {
    var key := arr_sorted[i];
    var j := i - 1;
    
    /* code modified by LLM (iteration 2): store original multiset before inner loop */
    ghost var original_multiset := multiset(arr_sorted[..]);
    
    while j >= 0 && arr_sorted[j] > key
      invariant -1 <= j < i
      invariant forall k :: j + 2 <= k <= i ==> arr_sorted[k] > key
      invariant forall k :: 0 <= k <= j ==> arr_sorted[k] <= arr_sorted[k+1] || k == j
      invariant sorted(arr_sorted, 0, j + 1)
      /* code modified by LLM (iteration 2): use ghost variable for multiset invariant */
      invariant multiset(arr_sorted[..]) == original_multiset
    {
      /* code modified by LLM (iteration 2): add assertion before shift to help verifier */
      ghost var before_shift := multiset(arr_sorted[..]);
      arr_sorted[j + 1] := arr_sorted[j];
      /* code modified by LLM (iteration 2): assert multiset preserved after shift */
      assert multiset(arr_sorted[..]) == before_shift;
      j := j - 1;
    }
    
    /* code modified by LLM (iteration 2): assert multiset before key insertion */
    ghost var before_insert := multiset(arr_sorted[..]);
    arr_sorted[j + 1] := key;
    /* code modified by LLM (iteration 2): assert multiset preserved after key insertion */
    assert multiset(arr_sorted[..]) == before_insert;
    
    /* code modified by LLM (iteration 2): prove sorted property is maintained */
    if j + 1 > 0 {
      assert forall k :: 0 <= k <= j ==> arr_sorted[k] <= key;
    }
    if j + 2 <= i {
      assert forall k :: j + 2 <= k <= i ==> key <= arr_sorted[k];
    }
    
    /* code modified by LLM (iteration 2): assert overall multiset equality maintained */
    assert multiset(arr_sorted[..]) == multiset(arr[..]);
    
    i := i + 1;
  }
}