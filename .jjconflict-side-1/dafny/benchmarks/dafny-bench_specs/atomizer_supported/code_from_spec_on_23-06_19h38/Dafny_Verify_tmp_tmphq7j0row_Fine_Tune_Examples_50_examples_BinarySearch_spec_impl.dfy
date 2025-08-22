//IMPL 
method BinarySearch(a: array<int>, key: int) returns (n: int)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures 0 <= n <= a.Length
    ensures forall i :: 0 <= i < n ==> a[i] < key
    ensures forall i :: n <= i < a.Length ==> key <= a[i]
{
    var left := 0;
    var right := a.Length;
    
    while left < right
        invariant 0 <= left <= right <= a.Length
        invariant forall i :: 0 <= i < left ==> a[i] < key
        invariant forall i :: right <= i < a.Length ==> key <= a[i]
    {
        var mid := left + (right - left) / 2;
        
        if a[mid] < key {
            left := mid + 1;
        } else {
            right := mid;
        }
    }
    
    n := left;
}