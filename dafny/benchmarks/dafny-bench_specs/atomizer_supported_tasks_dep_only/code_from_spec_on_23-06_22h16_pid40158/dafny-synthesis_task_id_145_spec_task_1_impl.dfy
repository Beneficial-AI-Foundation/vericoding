//IMPL 
method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
{
    var max := a[0];
    var min := a[0];
    var i := 1;
    
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> a[k] <= max
        invariant forall k :: 0 <= k < i ==> min <= a[k]
    {
        if a[i] > max {
            max := a[i];
        }
        if a[i] < min {
            min := a[i];
        }
        i := i + 1;
    }
    
    diff := max - min;
}