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
  arr_sorted := arr;
  
  var n := arr_sorted.Length;
  var i := 0;
  
  /* code modified by LLM (iteration 3): Corrected invariants to reflect actual bubble sort properties */
  while i < n
    invariant 0 <= i <= n
    invariant sorted(arr_sorted, n - i, n)
    invariant multiset(arr[..]) == multiset(arr_sorted[..])
    invariant i > 0 ==> (forall k :: n - i <= k < n ==> forall l :: 0 <= l < n - i ==> arr_sorted[l] <= arr_sorted[k])
  {
    var j := 0;
    /* code modified by LLM (iteration 3): Simplified inner loop invariants for bubble sort */
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant sorted(arr_sorted, n - i, n)
      invariant multiset(arr[..]) == multiset(arr_sorted[..])
      invariant i > 0 ==> (forall k :: n - i <= k < n ==> forall l :: 0 <= l < n - i ==> arr_sorted[l] <= arr_sorted[k])
      invariant forall k :: 0 <= k < j ==> arr_sorted[k] <= arr_sorted[j]
    {
      if arr_sorted[j] > arr_sorted[j + 1] {
        var temp := arr_sorted[j];
        arr_sorted[j] := arr_sorted[j + 1];
        arr_sorted[j + 1] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}