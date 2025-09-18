// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause to fix compilation error */
predicate IsSorted(a: array<int>) reads a {
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures (result >= 0 ==> (
        0 <= result < arr.Length &&
        arr[result] == target &&
        forall i :: 0 <= i < result ==> arr[i] != target
    )) &&
    (result == -1 ==> (
        forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): reviewed logic, no changes made pending verification results */
    var low := 0;
    var high := arr.Length;

    while low < high
        invariant 0 <= low <= high <= arr.Length
        invariant forall k :: 0 <= k < low ==> arr[k] < target
        invariant forall k :: high <= k < arr.Length ==> arr[k] >= target
    {
        var mid := low + (high - low) / 2;
        if arr[mid] < target {
            low := mid + 1;
        } else {
            high := mid;
        }
    }

    if low < arr.Length && arr[low] == target {
        result := low;
        assert forall i :: 0 <= i < result ==> arr[i] != target;
    } else {
        result := -1;
        assert forall i :: 0 <= i < arr.Length ==> arr[i] != target;
    }
}
// </vc-code>
