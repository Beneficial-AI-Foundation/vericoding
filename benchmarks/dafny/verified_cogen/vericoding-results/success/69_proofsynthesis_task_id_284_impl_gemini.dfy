// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AllElementsEquals(arr: array<int>, element: int) returns (result: bool)
    ensures result == (forall i :: 0 <= i < arr.Length ==> arr[i] == element)
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result == (forall k :: 0 <= k < i ==> arr[k] == element)
  {
    if arr[i] != element {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
