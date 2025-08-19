// IMPL
method MaxArray(a: array<int>) returns (max:int)
requires a.Length > 0
ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
ensures exists i :: 0 <= i < a.Length && a[i] == max
{
    max := a[0];
    var index := 0;
    
    while index < a.Length
        invariant 0 <= index <= a.Length
        invariant forall i :: 0 <= i < index ==> a[i] <= max
        invariant exists i :: 0 <= i < a.Length && a[i] == max
    {
        if a[index] > max {
            max := a[index];
        }
        index := index + 1;
    }
}