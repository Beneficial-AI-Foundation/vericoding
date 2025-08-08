//IMPL
method Max(a: array<int>) returns (res: int)
requires a.Length > 0
ensures exists i :: 0 <= i < a.Length && res == a[i]
ensures forall i :: 0 <= i < a.Length ==> a[i] <= res
{
    res := a[0];
    var j := 1;
    while j < a.Length
        invariant 1 <= j <= a.Length
        invariant exists i :: 0 <= i < j && res == a[i]
        invariant forall i :: 0 <= i < j ==> a[i] <= res
    {
        if a[j] > res {
            res := a[j];
        }
        j := j + 1;
    }
}