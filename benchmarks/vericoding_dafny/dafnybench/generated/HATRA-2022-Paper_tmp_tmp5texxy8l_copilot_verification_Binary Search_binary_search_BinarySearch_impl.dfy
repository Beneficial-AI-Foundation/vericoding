lemma DistinctImpliesNoDuplicates(arr: array<int>, i: int, j: int)
    requires distinct(arr)
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    requires i != j
    ensures arr[i] != arr[j]
{
    // This follows directly from the distinct predicate
}
// </vc-helpers>

// <vc-spec>
method BinarySearch(arr: array<int>, target: int) returns (index: int)
    requires distinct(arr)
    requires sorted(arr)
    ensures -1 <= index < arr.Length
    ensures index == -1 ==> not_found(arr, target)
    ensures index != -1 ==> found(arr, target, index)
// </vc-spec>
// <vc-code>
{
    var low := 0;
    var high := arr.Length - 1;
    
    while low <= high
        invariant 0 <= low <= arr.Length
        invariant -1 <= high < arr.Length
        invariant forall i :: 0 <= i < low ==> arr[i] < target
        invariant forall i :: high < i < arr.Length ==> arr[i] > target
    {
        var mid := low + (high - low) / 2;
        
        if arr[mid] == target {
            index := mid;
            return;
        } else if arr[mid] < target {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    
    index := -1;
}
// </vc-code>

// Predicate to check that the array is sorted
predicate sorted(a: array<int>)
reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k] 
}

// Predicate to that each element is unique
predicate distinct(arr: array<int>)
    reads arr
{
    forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j ==> arr[i] != arr[j]
}

// Predicate to that the target is not in the array
predicate not_found(arr: array<int>, target: int)
reads arr
{
    (forall j :: 0 <= j < arr.Length ==> arr[j] != target)
}

// Predicate to that the target is in the array
predicate found(arr: array<int>, target: int, index: int)
requires -1 <= index < arr.Length;
reads arr
{
    if index == -1 then false
    else if arr[index] == target then true
    else false
}