// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate BarrierProperty(arr: array<int>, p: int)
  reads arr
{
  forall k, l :: 0 <= k <= p && p < l < arr.Length ==> arr[k] < arr[l]
}
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
  result := BarrierProperty(arr, p);
}
// </vc-code>
