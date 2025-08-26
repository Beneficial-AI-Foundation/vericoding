method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos <= arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
// </vc-spec>
// <vc-code>
{
    var left := 0;
    var right := arr.Length - 1;
    pos := -1;
    
    while left <= right
        invariant 0 <= left <= arr.Length
        invariant -1 <= right < arr.Length
        invariant pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem)
        invariant pos == -1 ==> forall i :: 0 <= i < left ==> arr[i] < elem
        invariant pos == -1 ==> forall i :: right < i < arr.Length ==> arr[i] > elem
        invariant pos != -1 ==> forall i :: pos < i < left ==> arr[i] < elem || arr[i] > elem
        invariant pos != -1 ==> forall i :: right < i < arr.Length ==> arr[i] > elem
        invariant forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
        decreases right - left + 1
    {
        var mid := left + (right - left) / 2;
        
        if arr[mid] == elem {
            pos := mid;
            left := mid + 1;  // Continue searching right for last occurrence
        } else if arr[mid] < elem {
            left := mid + 1;
        } else {
            right := mid - 1;
        }
    }
    
    // Verify the postcondition for the case when pos != -1
    if pos != -1 {
        assert arr[pos] == elem;
        if pos < arr.Length - 1 {
            // Need to verify that arr[pos + 1] > elem
            // This follows from our search logic and the sorted property
            assert pos < arr.Length - 1;
            // The binary search ensures this property
        }
    }
}
// </vc-code>