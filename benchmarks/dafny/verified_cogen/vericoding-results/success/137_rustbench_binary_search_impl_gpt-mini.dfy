// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
function Mid(low: int, high: int): int { low + (high - low) / 2 }

lemma MidBounds(low: int, high: int)
  requires low <= high
  ensures low <= Mid(low, high) <= high
{
  assert 0 <= high - low;
  assert 0 <= (high - low) / 2 <= high - low;
  assert low <= low + (high - low) / 2 <= low + (high - low);
  assert low + (high - low) == high;
}
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
    invariant -1 <= high < arr.Length
    invariant forall k :: 0 <= k < low ==> arr[k] != target
    invariant forall k :: high < k < arr.Length ==> arr[k] != target
    decreases high - low + 1
  {
    var mid := Mid(low, high);
    MidBounds(low, high);
    if arr[mid] == target {
      result := Some(mid);
      return;
    } else if arr[mid] < target {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  result := None;
}
// </vc-code>
