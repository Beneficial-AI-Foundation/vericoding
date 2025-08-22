//ATOM sorted
// Predicate to determine whether the list is sorted between [start, stop)
predicate sorted(arr: array<int>, start: int, end: int)
requires 0 <= start <= end <= arr.Length
reads arr
{
  forall i, j :: start <= i <= j < end ==> arr[i] <= arr[j]
}

//IMPL sortArray
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
  /* code modified by LLM (iteration 1): Create new array instead of aliasing to avoid modifies clause issues */
  arr_sorted := new int[arr.Length];
  var k := 0;
  while k < arr.Length
    invariant 0 <= k <= arr.Length
    invariant forall idx :: 0 <= idx < k ==> arr_sorted[idx] == arr[idx]
  {
    arr_sorted[k] := arr[k];
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 1): Handle empty array case */
  if arr_sorted.Length == 0 {
    return;
  }
  
  var i := 1;
  while i < arr_sorted.Length
    invariant 1 <= i <= arr_sorted.Length
    invariant sorted(arr_sorted, 0, i)
    invariant multiset(arr[..]) == multiset(arr_sorted[..])
  {
    var key := arr_sorted[i];
    var j := i - 1;
    
    /* code modified by LLM (iteration 1): Simplified inner loop with correct invariants */
    while j >= 0 && arr_sorted[j] > key
      invariant -1 <= j < i
      invariant forall k :: j + 2 <= k <= i ==> arr_sorted[k] > key
      invariant forall k :: 0 <= k <= j ==> arr_sorted[k] <= arr_sorted[j]
      invariant sorted(arr_sorted, 0, j + 1)
      invariant multiset(arr_sorted[..]) == multiset(arr_sorted[..j+1] + [key] + arr_sorted[j+2..i] + arr_sorted[i+1..])
      decreases j
    {
      arr_sorted[j + 1] := arr_sorted[j];
      j := j - 1;
    }
    
    arr_sorted[j + 1] := key;
    
    /* code modified by LLM (iteration 1): Add assertion to help verification */
    assert sorted(arr_sorted, 0, i + 1);
    i := i + 1;
  }
}