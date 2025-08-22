// Predicate to determine whether the list is sorted between [start, stop)
predicate sorted(arr: array<int>, start: int, end: int)
requires 0 <= start <= end <= arr.Length
reads arr
{
    forall i, j :: start <= i <= j < end ==> arr[i] <= arr[j]
}

//IMPL sortArray
method sortArray(arr: array<int>) returns (arr_sorted: array<int>)
    // Requires array length to be between 0 and 10000
    requires 0 <= arr.Length < 10000
    // Ensuring the arry has been sorted
    ensures sorted(arr_sorted, 0, arr_sorted.Length)
    // Ensuring that we have not modified elements but have only changed their indices
    ensures multiset(arr[..]) == multiset(arr_sorted[..])

    // Modifies arr
    modifies arr
{
    var n := arr.Length;
    
    /* code modified by LLM (iteration 3): Create a new array to return instead of modifying and returning the same array */
    arr_sorted := new int[n];
    var k := 0;
    while k < n
        invariant 0 <= k <= n
        invariant arr_sorted.Length == n
        invariant forall idx :: 0 <= idx < k ==> arr_sorted[idx] == arr[idx]
    {
        arr_sorted[k] := arr[k];
        k := k + 1;
    }
    
    var i := 0;
    
    /* code modified by LLM (iteration 3): Fixed bubble sort implementation with correct invariants */
    while i < n
        invariant 0 <= i <= n
        invariant arr_sorted.Length == n
        invariant multiset(arr[..]) == multiset(arr_sorted[..])
        invariant forall p :: n - i <= p < n - 1 ==> arr_sorted[p] <= arr_sorted[p + 1]
        invariant forall p, q :: 0 <= p < n - i && n - i <= q < n ==> arr_sorted[p] <= arr_sorted[q]
    {
        var j := 0;
        /* code modified by LLM (iteration 3): Corrected inner loop for bubble sort with proper invariants */
        while j < n - i - 1
            invariant 0 <= j <= n - i - 1
            invariant arr_sorted.Length == n
            invariant multiset(arr[..]) == multiset(arr_sorted[..])
            invariant forall p :: n - i <= p < n - 1 ==> arr_sorted[p] <= arr_sorted[p + 1]
            invariant forall p, q :: 0 <= p < n - i && n - i <= q < n ==> arr_sorted[p] <= arr_sorted[q]
            invariant forall k :: 0 <= k < j ==> arr_sorted[k] <= arr_sorted[j]
        {
            if arr_sorted[j] > arr_sorted[j + 1] {
                /* code modified by LLM (iteration 3): Added swap operation */
                arr_sorted[j], arr_sorted[j + 1] := arr_sorted[j + 1], arr_sorted[j];
            }
            j := j + 1;
        }
        i := i + 1;
    }
}