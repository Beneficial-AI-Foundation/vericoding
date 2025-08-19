//IMPL 
method merging(a: array<int>, low: int, medium: int, high: int)
requires 0 <= low <= medium <= high < a.Length
modifies a
{
    // Create temporary arrays for the two subarrays
    var leftSize := medium - low + 1;
    var rightSize := high - medium;
    
    var left := new int[leftSize];
    var right := new int[rightSize];
    
    // Copy data to temporary arrays
    var i := 0;
    while i < leftSize
        invariant 0 <= i <= leftSize
    {
        left[i] := a[low + i];
        i := i + 1;
    }
    
    var j := 0;
    while j < rightSize
        invariant 0 <= j <= rightSize
    {
        right[j] := a[medium + 1 + j];
        j := j + 1;
    }
    
    // Merge the temporary arrays back into a[low..high]
    i := 0;
    j := 0;
    var k := low;
    
    while i < leftSize && j < rightSize
        invariant 0 <= i <= leftSize
        invariant 0 <= j <= rightSize
        invariant low <= k <= high + 1
        invariant k == low + i + j
    {
        if left[i] <= right[j] {
            a[k] := left[i];
            i := i + 1;
        } else {
            a[k] := right[j];
            j := j + 1;
        }
        k := k + 1;
    }
    
    // Copy remaining elements of left[], if any
    while i < leftSize
        invariant 0 <= i <= leftSize
        invariant low <= k <= high + 1
        invariant k == low + i + j
    {
        a[k] := left[i];
        i := i + 1;
        k := k + 1;
    }
    
    // Copy remaining elements of right[], if any
    while j < rightSize
        invariant 0 <= j <= rightSize
        invariant low <= k <= high + 1
        invariant k == low + i + j
    {
        a[k] := right[j];
        j := j + 1;
        k := k + 1;
    }
}