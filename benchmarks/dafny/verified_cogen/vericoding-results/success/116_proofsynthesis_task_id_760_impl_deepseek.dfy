// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate AllElementsEqual(arr: array<int>, start: int, end: int) requires 0 <= start <= end <= arr.Length reads arr { forall i,j :: start <= i < j < end ==> arr[i] == arr[j] }
/* helper modified by LLM (iteration 2): Added reads clause */
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(arr: array<int>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < arr.Length ==> arr[0] == arr[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed verification by ensuring proper array access */
  if arr.Length <= 1 {
    result := true;
  } else {
    result := AllElementsEqual(arr, 0, arr.Length);
  }
}
// </vc-code>
