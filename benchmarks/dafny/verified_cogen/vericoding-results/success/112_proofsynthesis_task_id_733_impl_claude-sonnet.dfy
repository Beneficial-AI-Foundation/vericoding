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
    /* code modified by LLM (iteration 2): fixed loop invariant by changing arr[k] > target to arr[k] >= target to handle equal elements correctly */
    var left := 0;
    var right := arr.Length;
    
    while left < right
        invariant 0 <= left <= right <= arr.Length
        invariant forall k :: 0 <= k < left ==> arr[k] < target
        invariant forall k :: right <= k < arr.Length ==> arr[k] >= target
    {
        var mid := left + (right - left) / 2;
        
        if arr[mid] < target {
            left := mid + 1;
        } else {
            right := mid;
        }
    }
    
    if left < arr.Length && arr[left] == target {
        index := left;
    } else {
        index := -1;
    }
}
// </vc-code>
