// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos <= arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := arr.Length - 1;

  while low <= high
    invariant 0 <= low <= arr.Length
    invariant -1 <= high < arr.Length
    invariant forall i :: 0 <= i < low ==> arr[i] <= elem
    invariant forall i :: high < i < arr.Length ==> arr[i] > elem
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
    pos := low - 1;
  } else {
    pos := -1;
  }
}
// </vc-code>
