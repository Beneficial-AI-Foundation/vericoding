//IMPL
method Max(a: array<int>) returns (res: int)
requires a.Length > 0
ensures exists i :: 0 <= i < a.Length && res == a[i]
ensures forall i :: 0 <= i < a.Length ==> a[i] <= res
{
    res := a[0];
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant exists j :: 0 <= j < i && res == a[j]
        invariant forall j :: 0 <= j < i ==> a[j] <= res
    {
        if a[i] > res {
            res := a[i];
        }
        i := i + 1;
    }
}