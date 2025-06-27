//IMPL
function GCDInt(a: int, b: int): int
requires a >= 0 && b >= 0
{
    if a == 0 then b
    else if b == 0 then a
    else if a >= b then GCDInt(a - b, b)
    else GCDInt(a, b - a)
}

method GCD(a: array<int>, b: array<int>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < a.Length ==> a[i] >= 0 && b[i] >= 0
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> GCDInt(a[i], b[i]) == res[i]
{
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
    invariant 0 <= i <= a.Length
    invariant res.Length == a.Length
    invariant forall j :: 0 <= j < i ==> GCDInt(a[j], b[j]) == res[j]
    {
        res[i] := GCDInt(a[i], b[i]);
        i := i + 1;
    }
}