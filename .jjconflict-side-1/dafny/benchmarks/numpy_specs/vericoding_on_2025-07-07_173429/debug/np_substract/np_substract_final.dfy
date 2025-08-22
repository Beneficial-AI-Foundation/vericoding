//IMPL
method Subtract(a: array<int>, b: array<int>) returns (res: array<int>)
requires a.Length == b.Length
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] - b[i]
{
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == a[j] - b[j]
    {
        res[i] := a[i] - b[i];
        i := i + 1;
    }
}