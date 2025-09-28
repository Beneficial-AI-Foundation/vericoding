// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function BinarySearchRange(arr: array<int>, target: int, low: int, high: int): (index: int)/* helper modified by LLM (iteration 3): added reads arr for array access and decreases for termination */
  reads arr
  requires 0 <= low <= high <= arr.Length
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures index == -1 ==> forall i :: low <= i < high ==> arr[i] != target
  ensures index != -1 ==> low <= index < high && arr[index] == target && forall i :: low <= i < index ==> arr[i] != target
  decreases high - low
{
  if low == high then
    -1
  else
    var mid := (low + high) / 2;
    if arr[mid] < target then
      BinarySearchRange(arr, target, mid + 1, high)
    else if arr[mid] > target then
      BinarySearchRange(arr, target, low, mid)
    else
      // Check if it's the first occurrence
      var left := BinarySearchRange(arr, target, low, mid);
      if left == -1 then
        mid
      else
        left
}
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures (result >= 0 ==> (
        0 <= result < arr.Length &&
        arr[result] == target &&
        forall i :: 0 <= i < result ==> arr[i] != target
    )) &&
    (result == -1 ==> (
        forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): unchanged as fixes are in helper */
{
  result := BinarySearchRange(arr, target, 0, arr.Length);
}
// </vc-code>
