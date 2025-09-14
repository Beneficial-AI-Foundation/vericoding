// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)

    requires
        forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]

    ensures
        if index >= 0 then (
            && 0 <= index < arr.Length
            && (forall k :: 0 <= k < index ==> arr[k] != target)
            && arr[index] == target
        ) else (
            forall k :: 0 <= k < arr.Length ==> arr[k] != target
        )
// </vc-spec>
// <vc-code>
{
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
        index := low;
    } else {
        index := -1;
    }
}
// </vc-code>
