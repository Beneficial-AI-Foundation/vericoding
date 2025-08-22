// IMPL 
method mergeSort(a: array<int>)
modifies a
{
    if a.Length <= 1 {
        return;
    }
    sorting(a, 0, a.Length - 1);
}

// IMPL 
method sorting(a: array<int>, low: int, high: int)
requires 0 <= low && high < a.Length
modifies a
/* code modified by LLM (iteration 2): Added decreases clause for termination */
decreases high - low
{
    if low < high {
        var medium := low + (high - low) / 2;
        /* code modified by LLM (iteration 2): Added assertion to ensure medium is in valid range and termination conditions */
        assert low <= medium < high;
        assert medium - low < high - low;
        assert high - (medium + 1) < high - low;
        sorting(a, low, medium);
        sorting(a, medium + 1, high);
        merging(a, low, medium, high);
    }
}

// IMPL 
method merging(a: array<int>, low: int, medium: int, high: int)
requires 0 <= low <= medium <= high < a.Length
modifies a
{
    var left := new int[medium - low + 1];
    var right := new int[high - medium];
    
    // Copy data to temporary arrays
    var i := 0;
    /* code modified by LLM (iteration 2): Added loop invariants for verification */
    while i < left.Length
    invariant 0 <= i <= left.Length
    invariant forall k :: 0 <= k < i ==> left[k] == a[low + k]
    {
        left[i] := a[low + i];
        i := i + 1;
    }
    
    var j := 0;
    /* code modified by LLM (iteration 2): Added loop invariants for verification */
    while j < right.Length
    invariant 0 <= j <= right.Length
    invariant forall k :: 0 <= k < j ==> right[k] == a[medium + 1 + k]
    {
        right[j] := a[medium + 1 + j];
        j := j + 1;
    }
    
    // Merge the temporary arrays back into a[low..high]
    i := 0;
    j := 0;
    var k := low;
    
    /* code modified by LLM (iteration 2): Added loop invariants for verification */
    while i < left.Length && j < right.Length
    invariant 0 <= i <= left.Length
    invariant 0 <= j <= right.Length
    invariant k == low + i + j
    invariant low <= k <= high + 1
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
    /* code modified by LLM (iteration 2): Added loop invariants for verification */
    while i < left.Length
    invariant 0 <= i <= left.Length
    invariant k == low + i + j
    invariant low <= k <= high + 1
    {
        a[k] := left[i];
        i := i + 1;
        k := k + 1;
    }
    
    // Copy remaining elements of right[], if any
    /* code modified by LLM (iteration 2): Added loop invariants for verification */
    while j < right.Length
    invariant 0 <= j <= right.Length
    invariant k == low + i + j
    invariant low <= k <= high + 1
    {
        a[k] := right[j];
        j := j + 1;
        k := k + 1;
    }
}