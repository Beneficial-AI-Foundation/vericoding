// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
        } else { // arr[mid] >= target
            high := mid;
        }
    }

    // After the loop, low == high, and 'low' is the index of the first element >= target, if any.
    // forall k :: 0 <= k < low ==> arr[k] < target
    // forall k :: low <= k < arr.Length ==> arr[k] >= target

    if low < arr.Length && arr[low] == target {
        result := low;
    } else {
        result := -1;
    }
}
// </vc-code>
