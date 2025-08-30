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
    arr_sorted := arr;
    
    if arr_sorted.Length <= 1 {
        return;
    }
    
    var i := 0;
    while i < arr_sorted.Length
        invariant 0 <= i <= arr_sorted.Length
        invariant multiset(arr[..]) == multiset(arr_sorted[..])
        /* code modified by LLM (iteration 3): maintain sorted property for processed elements */
        invariant sorted(arr_sorted, 0, i)
    {
        var j := i;
        while j > 0 && arr_sorted[j-1] > arr_sorted[j]
            invariant 0 <= j <= i
            invariant multiset(arr[..]) == multiset(arr_sorted[..])
            /* code modified by LLM (iteration 3): ensure proper sorted invariants for insertion sort */
            invariant sorted(arr_sorted, 0, j)
            invariant sorted(arr_sorted, j, i+1)
            invariant forall k1, k2 :: 0 <= k1 < j && j < k2 <= i ==> arr_sorted[k1] <= arr_sorted[k2]
        {
            arr_sorted[j-1], arr_sorted[j] := arr_sorted[j], arr_sorted[j-1];
            j := j - 1;
        }
        i := i + 1;
    }
}

// Predicate to determine whether the list is sorted between [start, stop)
//ATOM sorted
predicate sorted(arr: array<int>, start: int, end: int)
requires 0 <= start <= end <= arr.Length
reads arr
{
    forall i, j :: start <= i <= j < end ==> arr[i] <= arr[j]
}

// Predicate to determine whether element arr[pivot] is a pivot point
// Based on: https://github.com/stqam/dafny/blob/master/BubbleSort.dfy
//ATOM pivot
predicate pivot(arr: array<int>, pivot: int)
requires 0 <= pivot <= arr.Length
reads arr
{
    forall u, v :: 0 <= u < pivot < v < arr.Length ==> arr[u] <= arr[v]
}