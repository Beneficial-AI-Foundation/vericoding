//IMPL
method Abs(a: array<int>) returns (res: array<int>)
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == AbsInt(a[i])
ensures forall i :: 0 <= i < a.Length ==> res[i] >= 0
{
    res := new int[a.Length];
    for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> res[j] == AbsInt(a[j])
    invariant forall j :: 0 <= j < i ==> res[j] >= 0
    {
        if a[i] >= 0 {
            res[i] := a[i];
        } else {
            res[i] := -a[i];
        }
    }
}

function AbsInt(x: int): int
{
    if x >= 0 then x else -x
}