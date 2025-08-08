//IMPL
method Abs(a: array<int>) returns (res: array<int>)
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == (if a[i] < 0 then -a[i] else a[i])
ensures forall i :: 0 <= i < a.Length ==> res[i] >= 0
{
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == (if a[j] < 0 then -a[j] else a[j])
        invariant forall j :: 0 <= j < i ==> res[j] >= 0
    {
        if a[i] < 0 {
            res[i] := -a[i];
        } else {
            res[i] := a[i];
        }
        i := i + 1;
    }
}