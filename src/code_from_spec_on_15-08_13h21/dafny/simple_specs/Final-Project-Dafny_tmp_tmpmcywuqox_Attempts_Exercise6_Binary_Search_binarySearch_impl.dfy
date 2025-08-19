// IMPL
method binarySearch(a:array<int>, val:int) returns (pos:int)
 requires a.Length > 0
 requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]

 ensures 0 <= pos < a.Length ==> a[pos] == val
 ensures pos < 0 || pos >= a.Length ==> forall i :: 0 <= i < a.Length ==> a[i] != val

{
    var low := 0;
    var high := a.Length - 1;
    
    while low <= high
        invariant 0 <= low <= a.Length
        invariant -1 <= high < a.Length
        invariant forall i :: 0 <= i < low ==> a[i] < val
        invariant forall i :: high < i < a.Length ==> a[i] > val
    {
        var mid := (low + high) / 2;
        
        if a[mid] == val {
            pos := mid;
            return;
        } else if a[mid] < val {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    
    pos := -1;
}