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
    /* code modified by LLM (iteration 4): fixed invariant to allow equal values in sorted array */
    if arr.Length == 0 {
        result := -1;
        return;
    }
    
    var left := 0;
    var right := arr.Length;
    
    while left < right
        invariant 0 <= left <= right <= arr.Length
        invariant forall i :: 0 <= i < left ==> arr[i] < target
        invariant forall i :: right <= i < arr.Length ==> arr[i] >= target
    {
        var mid := left + (right - left) / 2;
        
        if arr[mid] < target {
            left := mid + 1;
        } else {
            right := mid;
        }
    }
    
    if left < arr.Length && arr[left] == target {
        result := left;
    } else {
        result := -1;
    }
}
// </vc-code>
