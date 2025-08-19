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
  var result := -1;
  
  /* code modified by LLM (iteration 1): Fixed loop invariants to properly track the search space and result validity */
  while left <= right
    invariant 0 <= left <= arr.Length
    invariant -1 <= right < arr.Length
    invariant result == -1 || (0 <= result < arr.Length && arr[result] == target)
    invariant forall i :: 0 <= i < left ==> arr[i] < target
    invariant forall i :: right < i < arr.Length ==> arr[i] > target
    invariant forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
    invariant result != -1 ==> (forall i :: 0 <= i < result ==> arr[i] < target)
    invariant result != -1 ==> left <= result
  {
    var mid := left + (right - left) / 2;
    
    if arr[mid] == target {
      result := mid;
      right := mid - 1;
    } else if arr[mid] < target {
      left := mid + 1;
    } else {
      right := mid - 1;
    }
  }
  
  /* code modified by LLM (iteration 1): Simplified post-condition verification logic */
  if result != -1 {
    // We found the target, and result is the leftmost occurrence
    assert arr[result] == target;
    assert forall i :: 0 <= i < result ==> arr[i] < target;
  } else {
    // No target found - prove the entire array doesn't contain target
    assert left > right;
    assert forall i :: 0 <= i < left ==> arr[i] < target;
    assert forall i :: right < i < arr.Length ==> arr[i] > target;
    
    /* code modified by LLM (iteration 1): Added explicit proof that covers all array indices */
    assert left == right + 1;
    forall i | 0 <= i < arr.Length
      ensures arr[i] != target
    {
      if i <= right {
        assert i < left;
        assert arr[i] < target;
      } else {
        assert i >= left;
        assert i > right;
        assert arr[i] > target;
      }
    }
  }
  
  return result;
}