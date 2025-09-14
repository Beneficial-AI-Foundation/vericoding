// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed array bounds in predicate */
predicate IsSorted(arr: array<int>, low: int, high: int)
    reads arr
    requires 0 <= low <= high <= arr.Length
{
    forall i, j :: low <= i < j < high ==> arr[i] <= arr[j]
}

lemma SortedSubarray(arr: array<int>, low: int, mid: int, high: int)
    requires 0 <= low <= mid <= high <= arr.Length
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures IsSorted(arr, low, high)
{
}
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
/* code modified by LLM (iteration 2): fixed array bounds issue */
{
    var low := 0;
    var high := arr.Length;
    
    while low < high
        invariant 0 <= low <= high <= arr.Length
        invariant forall i :: 0 <= i < low ==> arr[i] < target
        invariant forall i :: high <= i < arr.Length ==> arr[i] > target
    {
        var mid := low + (high - low) / 2;
        
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            low := mid + 1;
        } else {
            high := mid;
        }
    }
    
    return None;
}
// </vc-code>
