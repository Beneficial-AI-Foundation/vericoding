//ATOM

// Predicate to determine whether the list is sorted between [start, stop)
predicate sorted(arr: array<int>, start: int, end: int)
requires 0 <= start <= end <= arr.Length
reads arr
{
  forall i, j :: start <= i <= j < end ==> arr[i] <= arr[j]
}


// SPEC
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
}