// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method BinarySearch(arr: array<int>, target: int) returns (result: Option<int>)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures match result {
        case Some(index) => 0 <= index < arr.Length && arr[index] == target
        case None => forall i :: 0 <= i < arr.Length ==> arr[i] != target
    }
// </vc-spec>
// <vc-code>
{
    var low := 0;
    var high := arr.Length;
    while low < high
        invariant 0 <= low <= high <= arr.Length
        invariant forall i :: 0 <= i < low ==> arr[i] < target
        invariant forall i :: high <= i < arr.Length ==> target < arr[i]
    {
        var mid := low + (high - low) / 2;
        if arr[mid] < target {
            low := mid + 1;
        } else if arr[mid] > target {
            high := mid;
        } else {
            return Some(mid);
        }
    }
    return None;
}
// </vc-code>
