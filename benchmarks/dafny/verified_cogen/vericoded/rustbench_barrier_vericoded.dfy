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
  result := true;
  var i := 0;
  while i <= p
    invariant 0 <= i <= p + 1
    invariant result == forall k, l :: 0 <= k < i && p < l < arr.Length ==> arr[k] < arr[l]
  {
    var j := p + 1;
    while j < arr.Length
      invariant p + 1 <= j <= arr.Length
      invariant result == (forall k, l :: 0 <= k < i && p < l < arr.Length ==> arr[k] < arr[l]) && (forall l :: p < l < j ==> arr[i] < arr[l])
    {
      if arr[i] >= arr[j] {
        result := false;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
