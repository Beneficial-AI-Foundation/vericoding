// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(arr: array<int>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < arr.Length ==> arr[0] == arr[i])
// </vc-spec>
// <vc-code>
{
  if arr.Length <= 1 {
    return true;
  }

  var firstElement := arr[0];
  var i := 1;
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant forall k :: 1 <= k < i ==> arr[k] == firstElement
  {
    if arr[i] != firstElement {
      return false;
    }
    i := i + 1;
  }

  return true;
}
// </vc-code>
