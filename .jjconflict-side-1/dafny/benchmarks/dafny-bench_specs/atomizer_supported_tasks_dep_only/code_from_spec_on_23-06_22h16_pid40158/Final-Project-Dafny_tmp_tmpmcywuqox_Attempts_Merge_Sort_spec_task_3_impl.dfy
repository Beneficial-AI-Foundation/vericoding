//ATOM_PLACEHOLDER_mergeSort

//IMPL merging
method merging(a: array<int>, low: int, medium: int, high: int)
requires 0 <= low <= medium <= high < a.Length
modifies a
{
    var left := new int[medium - low + 1];
    var right := new int[high - medium];
    
    var i := 0;
    while i < left.Length
    invariant 0 <= i <= left.Length
    /* code modified by LLM (iteration 1): added bounds check invariant */
    invariant left.Length == medium - low + 1
    {
        /* code modified by LLM (iteration 1): added bounds check for array access */
        assert low + i < a.Length;
        left[i] := a[low + i];
        i := i + 1;
    }
    
    var j := 0;
    while j < right.Length
    invariant 0 <= j <= right.Length
    /* code modified by LLM (iteration 1): added bounds check invariant */
    invariant right.Length == high - medium
    {
        /* code modified by LLM (iteration 1): added bounds check for array access */
        assert medium + 1 + j <= high;
        assert medium + 1 + j < a.Length;
        right[j] := a[medium + 1 + j];
        j := j + 1;
    }
    
    i := 0;
    j := 0;
    var k := low;
    
    while i < left.Length && j < right.Length
    invariant 0 <= i <= left.Length
    invariant 0 <= j <= right.Length
    invariant low <= k <= high
    invariant k == low + i + j
    /* code modified by LLM (iteration 1): added array bounds invariants */
    invariant left.Length == medium - low + 1
    invariant right.Length == high - medium
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
    
    while i < left.Length
    invariant 0 <= i <= left.Length
    /* code modified by LLM (iteration 1): fixed upper bound for k */
    invariant low <= k <= high + 1
    invariant k == low + i + j
    /* code modified by LLM (iteration 1): added j bounds invariant */
    invariant 0 <= j <= right.Length
    invariant left.Length == medium - low + 1
    {
        a[k] := left[i];
        i := i + 1;
        k := k + 1;
    }
    
    while j < right.Length
    invariant 0 <= j <= right.Length
    /* code modified by LLM (iteration 1): fixed upper bound for k */
    invariant low <= k <= high + 1
    invariant k == low + i + j
    /* code modified by LLM (iteration 1): added i bounds invariant */
    invariant 0 <= i <= left.Length
    invariant right.Length == high - medium
    {
        a[k] := right[j];
        j := j + 1;
        k := k + 1;
    }
}

//IMPL sorting
method sorting(a: array<int>, low: int, high: int)
requires 0 <= low && high < a.Length
modifies a
/* code modified by LLM (iteration 1): added decreases clause for termination */
decreases high - low
{
    if low < high {
        var medium := low + (high - low) / 2;
        /* code modified by LLM (iteration 1): added assertion to help verification */
        assert low <= medium < high;
        sorting(a, low, medium);
        sorting(a, medium + 1, high);
        merging(a, low, medium, high);
    }
}