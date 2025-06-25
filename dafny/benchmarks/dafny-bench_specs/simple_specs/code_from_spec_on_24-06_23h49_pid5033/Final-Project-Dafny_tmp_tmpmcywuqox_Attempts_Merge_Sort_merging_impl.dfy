//IMPL merging
method merging(a: array<int>, low: int, medium: int, high: int)
requires 0 <= low <= medium <= high < a.Length
modifies a
{
    var temp := new int[high - low + 1];
    var i := low;
    var j := medium + 1;
    var k := 0;
    
    // Merge the two subarrays
    /* code modified by LLM (iteration 4): strengthened invariants to prove k < temp.Length */
    while i <= medium && j <= high
    invariant low <= i <= medium + 1
    invariant medium + 1 <= j <= high + 1
    invariant k == (i - low) + (j - (medium + 1))
    invariant 0 <= k <= high - low + 1
    invariant k <= temp.Length
    invariant (i <= medium && j <= high) ==> k < temp.Length
    invariant (i <= medium && j <= high) ==> k == (i - low) + (j - (medium + 1)) < (medium + 1 - low) + (high + 1 - (medium + 1))
    invariant (i <= medium && j <= high) ==> k < high - low + 1
    {
        if a[i] <= a[j] {
            temp[k] := a[i];
            i := i + 1;
        } else {
            temp[k] := a[j];
            j := j + 1;
        }
        k := k + 1;
    }
    
    // Copy remaining elements from left subarray
    /* code modified by LLM (iteration 4): strengthened invariants to prove k < temp.Length */
    while i <= medium
    invariant low <= i <= medium + 1
    invariant j == high + 1
    invariant k == (i - low) + (high + 1 - (medium + 1))
    invariant k == (i - low) + (high - medium)
    invariant 0 <= k <= high - low + 1
    invariant k <= temp.Length
    invariant i <= medium ==> k < temp.Length
    invariant i <= medium ==> (i - low) + (high - medium) < high - low + 1
    {
        temp[k] := a[i];
        i := i + 1;
        k := k + 1;
    }
    
    // Copy remaining elements from right subarray
    /* code modified by LLM (iteration 4): strengthened invariants to prove k < temp.Length */
    while j <= high
    invariant i == medium + 1
    invariant medium + 1 <= j <= high + 1
    invariant k == (medium + 1 - low) + (j - (medium + 1))
    invariant k == j - low
    invariant 0 <= k <= high - low + 1
    invariant k <= temp.Length
    invariant j <= high ==> k < temp.Length
    invariant j <= high ==> j - low < high - low + 1
    {
        temp[k] := a[j];
        j := j + 1;
        k := k + 1;
    }
    
    // Copy merged elements back to original array
    k := 0;
    i := low;
    /* code modified by LLM (iteration 4): strengthened invariants to prove k < temp.Length */
    while i <= high
    invariant low <= i <= high + 1
    invariant k == i - low
    invariant 0 <= k <= high - low + 1
    invariant k <= temp.Length
    invariant i <= high ==> k < temp.Length
    invariant i <= high ==> i - low < high - low + 1
    {
        a[i] := temp[k];
        i := i + 1;
        k := k + 1;
    }
}