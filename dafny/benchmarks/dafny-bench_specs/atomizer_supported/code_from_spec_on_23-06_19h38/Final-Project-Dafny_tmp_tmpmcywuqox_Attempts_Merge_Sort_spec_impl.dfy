// IMPL 
method mergeSort(a: array<int>)
modifies a
{
    if a.Length > 1 {
        sorting(a, 0, a.Length - 1);
    }
}

// IMPL 
method merging(a: array<int>, low: int, medium: int, high: int)
requires 0 <= low <= medium <= high < a.Length
modifies a
{
    var leftSize := medium - low + 1;
    var rightSize := high - medium;
    
    var left := new int[leftSize];
    var right := new int[rightSize];
    
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
    
    i := 0;
    j := 0;
    var k := low;
    
    while i < leftSize && j < rightSize
        invariant 0 <= i <= leftSize
        invariant 0 <= j <= rightSize
        invariant k == low + i + j
        invariant low <= k <= high
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
    
    while i < leftSize
        invariant 0 <= i <= leftSize
        invariant j == rightSize
        invariant k == low + i + j
        /* code modified by LLM (iteration 4): fixed upper bound to allow k to reach high + 1 */
        invariant low <= k <= high + 1
    {
        a[k] := left[i];
        i := i + 1;
        k := k + 1;
    }
    
    while j < rightSize
        invariant 0 <= j <= rightSize
        invariant i == leftSize
        invariant k == low + i + j
        /* code modified by LLM (iteration 4): fixed upper bound to allow k to reach high + 1 */
        invariant low <= k <= high + 1
    {
        a[k] := right[j];
        j := j + 1;
        k := k + 1;
    }
}

// IMPL 
method sorting(a: array<int>, low: int, high: int)
/* code modified by LLM (iteration 4): fixed preconditions to handle edge cases and recursion properly */
requires 0 <= low <= high < a.Length
modifies a
{
    if low < high {
        var medium := low + (high - low) / 2;
        sorting(a, low, medium);
        sorting(a, medium + 1, high);
        merging(a, low, medium, high);
    }
}