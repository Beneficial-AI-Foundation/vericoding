//IMPL
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
  requires arr != null
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures 0 <= index < arr.Length ==> arr[index] == target
  ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
  ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
  if arr.Length == 0 {
    return -1;
  }
  
  var left := 0;
  var right := arr.Length - 1;
  index := -1;
  
  /* code modified by LLM (iteration 4): simplified and corrected loop invariants for first occurrence search */
  while left <= right
    invariant 0 <= left <= arr.Length
    invariant -1 <= right < arr.Length
    invariant forall i :: 0 <= i < left ==> arr[i] < target
    invariant forall i :: right < i < arr.Length ==> arr[i] > target
    invariant index == -1 || (0 <= index < arr.Length && arr[index] == target)
    invariant index != -1 ==> (left <= index <= right + 1 && forall i :: 0 <= i < index ==> arr[i] < target)
    decreases right - left + 1
  {
    var mid := (left + right) / 2;
    
    if arr[mid] == target {
      index := mid;
      /* code modified by LLM (iteration 4): continue searching left to find first occurrence */
      right := mid - 1;
    } else if arr[mid] < target {
      left := mid + 1;
    } else {
      right := mid - 1;
    }
  }
  
  /* code modified by LLM (iteration 4): added assertions to help prove postconditions */
  if index != -1 {
    assert arr[index] == target;
    assert forall i :: 0 <= i < index ==> arr[i] < target;
  } else {
    assert forall i :: 0 <= i < left ==> arr[i] < target;
    assert forall i :: right < i < arr.Length ==> arr[i] > target;
    assert left > right;
    assert forall i :: 0 <= i < arr.Length ==> arr[i] != target;
  }
}