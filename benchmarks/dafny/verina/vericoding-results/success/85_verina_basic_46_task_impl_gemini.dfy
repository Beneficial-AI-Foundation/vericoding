// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed lemma to method to allow non-ghost calls */
method UpperBound(arr: array<int>, elem: int) returns (idx: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= idx <= arr.Length
    ensures forall i :: 0 <= i < idx ==> arr[i] <= elem
    ensures forall i :: idx <= i < arr.Length ==> arr[i] > elem
{
    var low := 0;
    var high := arr.Length;
    while low < high
        decreases high - low
        invariant 0 <= low <= high <= arr.Length
        invariant forall i :: 0 <= i < low ==> arr[i] <= elem
        invariant forall i :: high <= i < arr.Length ==> arr[i] > elem
    {
        var mid := low + (high - low) / 2;
        if arr.Length > 0 && mid < arr.Length && arr[mid] > elem { // Added bounds check for safety
            high := mid;
        } else {
            low := mid + 1;
        }
    }
    idx := low;
}
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
    /* code modified by LLM (iteration 2): calling method instead of lemma to fix ghost context error */
    var upper_bound_idx := UpperBound(arr, elem);
    if upper_bound_idx > 0 && arr[upper_bound_idx - 1] == elem {
        result := upper_bound_idx - 1;
    } else {
        result := -1;
    }
}
// </vc-code>
