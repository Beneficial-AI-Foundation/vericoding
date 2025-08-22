//ATOM
function sorted(a: array<int>) : bool
    reads a
{
   forall i,j : int :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

//IMPL
method BinarySearch(a: array<int>, x: int) returns (index: int)
    requires sorted(a)
    ensures 0 <= index < a.Length ==> a[index] == x
    ensures index == -1 ==> forall i : int :: 0 <= i < a.Length ==> a[i] != x
{
    if a.Length == 0 {
        index := -1;
        return;
    }
    
    var low := 0;
    var high := a.Length - 1;
    
    while low <= high
        invariant 0 <= low <= a.Length
        invariant -1 <= high < a.Length
        invariant forall i : int :: 0 <= i < low ==> a[i] < x
        invariant forall i : int :: high < i < a.Length ==> a[i] > x
    {
        var mid := (low + high) / 2;
        
        if a[mid] == x {
            index := mid;
            return;
        } else if a[mid] < x {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    
    index := -1;
}