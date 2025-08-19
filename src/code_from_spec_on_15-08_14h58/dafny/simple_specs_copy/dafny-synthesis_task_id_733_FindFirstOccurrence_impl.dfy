method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
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
  
  /* code modified by LLM (iteration 4): improved loop invariants for better coverage */
  while left <= right
    invariant 0 <= left <= arr.Length
    invariant -1 <= right < arr.Length
    invariant index == -1 || (0 <= index < arr.Length && arr[index] == target)
    invariant forall i :: 0 <= i < left ==> arr[i] < target
    invariant forall i :: right < i < arr.Length ==> arr[i] > target || (arr[i] == target && index != -1)
    invariant index == -1 ==> forall i :: 0 <= i < left ==> arr[i] != target
    invariant index == -1 ==> forall i :: right < i < arr.Length ==> arr[i] != target
  {
    var mid := left + (right - left) / 2;
    
    if arr[mid] == target {
      index := mid;
      right := mid - 1;  // Continue searching left for first occurrence
    } else if arr[mid] < target {
      left := mid + 1;
    } else {
      right := mid - 1;
    }
  }
  
  /* code modified by LLM (iteration 4): improved proof with better range coverage */
  if index == -1 {
    assert forall i :: 0 <= i < left ==> arr[i] != target;
    assert forall i :: right < i < arr.Length ==> arr[i] != target;
    assert left > right;
    /* code modified by LLM (iteration 4): explicit proof that ranges cover entire array */
    assert forall i :: 0 <= i < arr.Length ==> (i < left || i > right);
    assert forall i :: 0 <= i < arr.Length ==> arr[i] != target;
  }
}