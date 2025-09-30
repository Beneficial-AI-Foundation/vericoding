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
    var left := 0;
    var right := arr.Length;
    
    while left < right
        invariant 0 <= left <= right <= arr.Length
        invariant forall i :: 0 <= i < left ==> arr[i] < target
        invariant forall i :: right <= i < arr.Length ==> arr[i] > target
    {
        var mid := left + (right - left) / 2;
        
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            left := mid + 1;
        } else {
            right := mid;
        }
    }
    
    return None;
}
// </vc-code>
