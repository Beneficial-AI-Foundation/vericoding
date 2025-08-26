// <vc-helpers>
// Helper lemmas can be added here if needed for verification
// </vc-helpers>

// <vc-spec>
method sortArray(arr: array<int>) returns (arr_sorted: array<int>)
    // Requires array length to be between 0 and 10000
    requires 0 <= arr.Length < 10000
    // Ensuring the arry has been sorted
    ensures sorted(arr_sorted, 0, arr_sorted.Length)
    // Ensuring that we have not modified elements but have only changed their indices
    ensures multiset(arr[..]) == multiset(arr_sorted[..])

    // Modifies arr
    modifies arr
// </vc-spec>
// <vc-code>
{
    var originalMultiset := multiset(arr[..]);
    
    // Selection sort implementation
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant sorted(arr, 0, i)
        invariant multiset(arr[..]) == originalMultiset
        invariant forall x, y :: 0 <= x < i <= y < arr.Length ==> arr[x] <= arr[y]
    {
        // Find minimum element in arr[i..arr.Length)
        var minIndex := i;
        var j := i + 1;
        
        while j < arr.Length
            invariant i < j <= arr.Length
            invariant i <= minIndex < j
            invariant forall k :: i <= k < j ==> arr[minIndex] <= arr[k]
        {
            if arr[j] < arr[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        
        // Swap arr[i] and arr[minIndex]
        if i != minIndex {
            var temp := arr[i];
            arr[i] := arr[minIndex];
            arr[minIndex] := temp;
        }
        
        i := i + 1;
    }
    
    arr_sorted := arr;
}
// </vc-code>

// Predicate to determine whether the list is sorted between [start, stop)
predicate sorted(arr: array<int>, start: int, end: int)
requires 0 <= start <= end <= arr.Length
reads arr
{
    forall i, j :: start <= i <= j < end ==> arr[i] <= arr[j]
}

// Predicate to determine whether element arr[pivot] is a pivot point
// Based on: https://github.com/stqam/dafny/blob/master/BubbleSort.dfy
predicate pivot(arr: array<int>, pivot: int)
requires 0 <= pivot <= arr.Length
reads arr
{
    forall u, v :: 0 <= u < pivot < v < arr.Length ==> arr[u] <= arr[v]
}