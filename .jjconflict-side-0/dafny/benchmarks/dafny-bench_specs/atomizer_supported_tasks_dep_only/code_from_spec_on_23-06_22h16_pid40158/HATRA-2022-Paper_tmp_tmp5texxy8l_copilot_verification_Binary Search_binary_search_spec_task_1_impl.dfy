// Dafny verification of binary search alogirthm from binary_search.py
// Inspired by: https://ece.uwaterloo.ca/~agurfink/stqam/rise4fun-Dafny/#h211

//IMPL BinarySearch
method BinarySearch(arr: array<int>, target: int) returns (index: int)
    requires distinct(arr)
    requires sorted(arr)
    ensures -1 <= index < arr.Length
    ensures index == -1 ==> not_found(arr, target)
    ensures index != -1 ==> found(arr, target, index)
{
    var low := 0;
    var high := arr.Length;
    
    while low < high
        invariant 0 <= low <= high <= arr.Length
        invariant forall i :: 0 <= i < low ==> arr[i] < target
        invariant forall i :: high <= i < arr.Length ==> arr[i] > target
    {
        var mid := (low + high) / 2;
        
        if arr[mid] < target {
            low := mid + 1;
        } else if arr[mid] > target {
            high := mid;
        } else {
            index := mid;
            return;
        }
    }
    
    index := -1;
}

//ATOM sorted
// Predicate to check that the array is sorted
predicate sorted(a: array<int>)
reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k] 
}

//ATOM distinct
// Predicate to that each element is unique
predicate distinct(arr: array<int>)
    reads arr
{
    forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j ==> arr[i] != arr[j]
}

//ATOM not_found
// Predicate to that the target is not in the array
predicate not_found(arr: array<int>, target: int)
reads arr
{
    (forall j :: 0 <= j < arr.Length ==> arr[j] != target)
}

//ATOM found
// Predicate to that the target is in the array
predicate found(arr: array<int>, target: int, index: int)
requires -1 <= index < arr.Length;
reads arr
{
    if index == -1 then false
    else if arr[index] == target then true
    else false
}