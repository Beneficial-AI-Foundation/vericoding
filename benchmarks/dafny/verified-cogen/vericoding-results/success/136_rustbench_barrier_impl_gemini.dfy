// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Barrier(arr: array<int>, p: int) returns (result: bool)
    requires
        arr.Length > 0 &&
        0 <= p < arr.Length
    ensures
        result == forall k, l :: 0 <= k <= p && p < l < arr.Length ==> arr[k] < arr[l]
// </vc-spec>
// <vc-code>
{
  var k := 0;
  while k <= p
    invariant 0 <= k <= p + 1
    invariant forall i, j :: 0 <= i < k && p < j < arr.Length ==> arr[i] < arr[j]
  {
    var l := p + 1;
    while l < arr.Length
      invariant p + 1 <= l <= arr.Length
      invariant forall i, j :: 0 <= i < k && p < j < arr.Length ==> arr[i] < arr[j]
      invariant forall j :: p < j < l ==> arr[k] < arr[j]
    {
      if arr[k] >= arr[l] {
        result := false;
        return;
      }
      l := l + 1;
    }
    k := k + 1;
  }
  result := true;
  return;
}
// </vc-code>
