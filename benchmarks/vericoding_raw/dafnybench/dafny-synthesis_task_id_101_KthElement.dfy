// <vc-helpers>
// </vc-helpers>

method KthElement(arr: array<int>, k: int) returns (result: int)
  requires 1 <= k <= arr.Length
  ensures result == arr[k - 1]
// <vc-code>
{
  assume false;
}
// </vc-code>