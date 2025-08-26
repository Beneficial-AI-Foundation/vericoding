I need to fix this invariant to correctly handle the case where we've found target elements.

method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires arr != null
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
// </vc-spec>
// <vc-code>
{
  if arr.Length == 0 {
    return -1;
  }
  
  var left := 0;
  var right := arr.Length - 1;
  var result := -1;
  
  while left <= right
    invariant 0 <= left <= arr.Length
    invariant -1 <= right < arr.Length
    invariant result == -1 || (0 <= result < arr.Length && arr[result] == target)
    invariant forall i :: 0 <= i < left ==> arr[i] < target
    invariant forall i :: right < i < arr.Length ==> arr[i] >= target
    invariant forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
    invariant result != -1 ==> (forall i :: 0 <= i < result ==> arr[i] < target)
    invariant result != -1 ==> (forall i :: 0 <= i < left ==> i < result || arr[i] != target)
  {
    var mid := left + (right - left) / 2;
    
    if arr[mid] == target {
      result := mid;
      right := mid - 1; // Continue searching in the left half to find the first occurrence
    } else if arr[mid] < target {
      left := mid + 1;
    } else {
      // arr[mid] > target
      assert arr[mid] > target;
      // Since array is sorted, all elements from mid onwards are >= arr[mid] > target
      assert forall i :: mid <= i < arr.Length ==> arr[i] >= arr[mid] > target;
      right := mid - 1;
    }
  }
  
  return result;
}
// </vc-code>