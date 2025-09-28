// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LastPosition(arr: array<int>, elem: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures
        (result >= 0 ==> 
            0 <= result < arr.Length &&
            arr[result] == elem &&
            forall k :: result < k < arr.Length ==> arr[k] != elem) &&
        (result == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != elem)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Separated decreases clause from invariants to fix compilation error, ensured termination and correctness for finding last position of element in sorted array. */
  if arr.Length == 0 {
    result := -1;
  } else {
    var low := 0;
    var high := arr.Length - 1;
    while low <= high
      invariant 0 <= low <= high + 1 <= arr.Length
      invariant arr.Length > 0
      invariant forall i :: 0 <= i < low ==> arr[i] <= elem
      invariant forall i :: high + 1 <= i < arr.Length ==> arr[i] > elem
      decreases high - low
    {
      var mid := low + (high - low) / 2;
      if arr[mid] <= elem {
        low := mid + 1;
      } else {
        high := mid - 1;
      }
    }
    if low > 0 && arr[low - 1] == elem {
      result := low - 1;
    } else {
      result := -1;
    }
  }
}
// </vc-code>
