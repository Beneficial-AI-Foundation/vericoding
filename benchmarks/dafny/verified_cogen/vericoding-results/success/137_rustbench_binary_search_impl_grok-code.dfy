// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method BinarySearch(arr: array<int>, target: int) returns (result: Option<int>)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures match result {
        case Some(index) => 0 <= index < arr.Length && arr[index] == target
        case None => forall i :: 0 <= i < arr.Length ==> arr[i] != target
    }
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := arr.Length - 1;
  while low <= high
    invariant 0 <= low <= arr.Length
    invariant high < arr.Length || high >= arr.Length
    invariant -1 <= high <= arr.Length - 1
    invariant forall k :: 0 <= k < low ==> arr[k] < target || arr[k] != target
    invariant forall k :: high < k < arr.Length ==> arr[k] > target || arr[k] != target
  {
    var mid := low + (high - low) / 2;
    if arr[mid] == target {
      return Some(mid);
    } else if arr[mid] < target {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  return None;
}
// </vc-code>
