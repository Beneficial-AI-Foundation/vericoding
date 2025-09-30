

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos <= arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
// </vc-spec>
// <vc-code>
{
    var low := 0;
    var high := arr.Length - 1;
    pos := -1;
    
    while low <= high
        invariant 0 <= low <= arr.Length
        invariant -1 <= high < arr.Length
        invariant pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem)
        invariant forall i :: 0 <= i < low ==> arr[i] < elem || (arr[i] == elem && pos != -1)
        invariant forall i :: high < i < arr.Length ==> arr[i] > elem || (arr[i] == elem && 0 <= pos <= i)
    {
        var mid := (low + high) / 2;
        
        if arr[mid] == elem {
            pos := mid;
            low := mid + 1;  // Continue searching to the right for the last occurrence
        } else if arr[mid] < elem {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
}
// </vc-code>

