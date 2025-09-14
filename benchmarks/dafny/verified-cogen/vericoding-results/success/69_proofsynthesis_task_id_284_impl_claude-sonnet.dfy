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
  if arr.Length == 0 {
    result := true;
    return;
  }
  
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> arr[j] == element
  {
    if arr[i] != element {
      result := false;
      return;
    }
    i := i + 1;
  }
  
  result := true;
}
// </vc-code>
