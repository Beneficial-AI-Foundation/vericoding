//IMPL 
method MaxArray(a: array<int>) returns (max:int)
requires a.Length > 0
ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
ensures exists i :: 0 <= i < a.Length && a[i] == max
{
    max := a[0];
    var j := 1;
    while j < a.Length
        invariant 1 <= j <= a.Length
        invariant forall k :: 0 <= k < j ==> a[k] <= max
        invariant exists k :: 0 <= k < j && a[k] == max
    {
        if a[j] > max {
            max := a[j];
        }
        j := j + 1;
    }
}