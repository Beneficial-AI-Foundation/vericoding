//ATOM

// Predicate to determine whether the list is sorted between [start, stop)
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
  
  // Copy elements from original array
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> arr_sorted[k] == arr[k]
  {
    arr_sorted[i] := arr[i];
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Added assertion to establish multiset equality after copying */
  assert multiset(arr[..]) == multiset(arr_sorted[..]);
  
  // Simple insertion sort
  var j := 1;
  while j < arr_sorted.Length
    invariant 1 <= j <= arr_sorted.Length
    invariant sorted(arr_sorted, 0, j)
    invariant multiset(arr[..]) == multiset(arr_sorted[..])
  {
    var key := arr_sorted[j];
    var k := j - 1;
    
    /* code modified by LLM (iteration 1): Fixed inner loop invariants and added ghost variable for multiset tracking */
    ghost var old_arr_sorted := arr_sorted[..];
    
    while k >= 0 && arr_sorted[k] > key
      invariant -1 <= k < j
      invariant forall m :: k + 2 <= m <= j ==> arr_sorted[m] > key
      invariant forall m :: 0 <= m <= k ==> arr_sorted[m] <= arr_sorted[m+1] || m == k
      invariant forall m :: k + 2 <= m < j ==> arr_sorted[m] <= arr_sorted[m+1]
      invariant sorted(arr_sorted, 0, k + 1)
      invariant sorted(arr_sorted, k + 2, j + 1)
      invariant multiset(old_arr_sorted) == multiset(arr_sorted[..])
      invariant multiset(arr[..]) == multiset(arr_sorted[..])
      decreases k
    {
      arr_sorted[k + 1] := arr_sorted[k];
      k := k - 1;
    }
    
    arr_sorted[k + 1] := key;
    
    /* code modified by LLM (iteration 1): Added lemma call and assertions to help verification */
    assert arr_sorted[k + 1] == key;
    assert forall m :: 0 <= m <= k ==> arr_sorted[m] <= key;
    assert forall m :: k + 2 <= m <= j ==> arr_sorted[m] >= key;
    assert sorted(arr_sorted, 0, j + 1);
    
    j := j + 1;
  }
}