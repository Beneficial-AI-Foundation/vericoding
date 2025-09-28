// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed helper function due to type mismatch with array slicing */
// </vc-helpers>

// <vc-spec>
method MinSecondValueFirst(arr: array<array<int>>) returns (first_of_min_second: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> arr[i].Length >= 2
    ensures exists i :: (0 <= i < arr.Length && first_of_min_second == arr[i][0] && 
            (forall j :: 0 <= j < arr.Length ==> arr[i][1] <= arr[j][1]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented iterative search for minimum second value */
{
  var min_idx := 0;
  var min_second := arr[0][1];
  
  var i := 1;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= min_idx < i
    invariant min_second == arr[min_idx][1]
    invariant forall j :: 0 <= j < i ==> arr[min_idx][1] <= arr[j][1]
  {
    if arr[i][1] < min_second {
      min_idx := i;
      min_second := arr[i][1];
    }
    i := i + 1;
  }
  
  first_of_min_second := arr[min_idx][0];
}
// </vc-code>
