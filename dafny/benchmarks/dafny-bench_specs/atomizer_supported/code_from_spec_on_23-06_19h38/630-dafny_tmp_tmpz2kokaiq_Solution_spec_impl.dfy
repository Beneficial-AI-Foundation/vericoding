// ATOM 

function sorted(a: array<int>) : bool
    reads a
{
   forall i,j : int :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// IMPL 

method BinarySearch(a: array<int>, x: int) returns (index: int)
    requires sorted(a)
    ensures 0 <= index < a.Length ==> a[index] == x
    ensures index == -1 ==> forall i : int :: 0 <= i < a.Length ==> a[i] != x
{
    var low := 0;
    var high := a.Length;
    
    while low < high
        invariant 0 <= low <= high <= a.Length
        invariant forall i : int :: 0 <= i < low ==> a[i] < x
        invariant forall i : int :: high <= i < a.Length ==> a[i] > x
    {
        var mid := (low + high) / 2;
        
        if a[mid] < x {
            low := mid + 1;
        } else if a[mid] > x {
            high := mid;
        } else {
            index := mid;
            return;
        }
    }
    
    index := -1;
}