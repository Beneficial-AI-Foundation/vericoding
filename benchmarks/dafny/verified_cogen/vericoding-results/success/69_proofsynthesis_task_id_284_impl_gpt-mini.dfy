// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause so predicate can read array elements */
predicate IsAllEqual(arr: array<int>, element: int) reads arr { forall i :: 0 <= i < arr.Length ==> arr[i] == element }
// </vc-helpers>

// <vc-spec>
method AllElementsEquals(arr: array<int>, element: int) returns (result: bool)
    ensures result == (forall i :: 0 <= i < arr.Length ==> arr[i] == element)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate and return on first mismatch */
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> arr[j] == element
  {
    if arr[i] != element {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>
