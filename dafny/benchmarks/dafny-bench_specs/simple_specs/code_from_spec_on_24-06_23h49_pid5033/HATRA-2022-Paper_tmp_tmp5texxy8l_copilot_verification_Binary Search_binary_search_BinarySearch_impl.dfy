//ATOM

// Predicate to that the target is not in the array
predicate not_found(arr: array<int>, target: int)
reads arr
{
  (forall j :: 0 <= j < arr.Length ==> arr[j] != target)
}


//ATOM

// Predicate to that the target is in the array
predicate found(arr: array<int>, target: int, index: int)
requires -1 <= index < arr.Length
reads arr
{
  if index == -1 then false
  else if arr[index] == target then true
  else false
}


//ATOM

// Predicate to check that the array is sorted
predicate sorted(a: array<int>)
reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k] 
}


//ATOM

// Predicate to that each element is unique
predicate distinct(arr: array<int>)
  reads arr
{
  forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length ==> arr[i] != arr[j]
}


//IMPL BinarySearch
method BinarySearch(arr: array<int>, target: int) returns (index: int)
  requires distinct(arr)
  requires sorted(arr)
  ensures -1 <= index < arr.Length
  ensures index == -1 ==> not_found(arr, target)
  ensures index != -1 ==> found(arr, target, index)
{
  if arr.Length == 0 {
    return -1;
  }
  
  var left := 0;
  var right := arr.Length - 1;
  
  while left <= right
    invariant 0 <= left <= arr.Length
    invariant -1 <= right < arr.Length
    invariant left <= right + 1
    invariant forall k :: 0 <= k < left ==> arr[k] < target
    invariant forall k :: right < k < arr.Length ==> arr[k] > target
  {
    var mid := left + (right - left) / 2;
    
    if arr[mid] == target {
      return mid;
    } else if arr[mid] < target {
      left := mid + 1;
    } else {
      right := mid - 1;
    }
  }
  
  return -1;
}