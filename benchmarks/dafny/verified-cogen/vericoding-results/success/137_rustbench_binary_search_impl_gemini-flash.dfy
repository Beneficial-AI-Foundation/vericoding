// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
function Mid(low: int, high: int): int { low + (high - low) / 2 }
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
    var high := arr.Length - 1;

    while low <= high
        invariant 0 <= low <= arr.Length
        invariant -1 <= high < arr.Length
        invariant forall i :: 0 <= i < low ==> arr[i] != target
        invariant forall i :: high < i < arr.Length ==> arr[i] != target
    {
        var mid := Mid(low, high);

        if mid < 0 || mid >= arr.Length {
            // This case should not be reached if invariants hold, but good for robustness
            break;
        }

        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }

    return None;
}
// </vc-code>
