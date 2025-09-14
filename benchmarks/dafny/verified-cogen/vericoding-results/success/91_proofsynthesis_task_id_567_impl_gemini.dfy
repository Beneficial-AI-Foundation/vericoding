// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSorted(arr: array<int>) returns (is_sorted: bool)

    requires
        arr.Length > 0

    ensures
        is_sorted == (forall i, j :: 0 <= i < j < arr.Length ==> (arr[i] <= arr[j]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): used a stronger loop invariant */
{
  var i: nat := 1;
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant forall j, k :: 0 <= j < k < i ==> arr[j] <= arr[k]
  {
    if arr[i-1] > arr[i] {
        is_sorted := false;
        return;
    }
    i := i + 1;
  }
  is_sorted := true;
}
// </vc-code>
