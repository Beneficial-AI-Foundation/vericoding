// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsGreater(arr: array<int>, number: int) returns (result: bool)
    ensures result == (forall i :: 0 <= i < arr.Length ==> number > arr[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> number > arr[k]
  {
    if arr[i] >= number {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>
