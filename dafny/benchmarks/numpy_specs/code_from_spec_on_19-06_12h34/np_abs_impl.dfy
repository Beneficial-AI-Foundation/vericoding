//IMPL
function AbsInt(x: int): int
{
    if x >= 0 then x else -x
}

method Abs(a: array<int>) returns (res: array<int>)
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == AbsInt(a[i])
ensures forall i :: 0 <= i < a.Length ==> res[i] >= 0
{
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == AbsInt(a[j])
        invariant forall j :: 0 <= j < i ==> res[j] >= 0
    {
        /* code modified by LLM (iteration 1): Use AbsInt function directly and add assertion to help verification */
        res[i] := AbsInt(a[i]);
        assert res[i] == AbsInt(a[i]);
        assert res[i] >= 0;
        i := i + 1;
    }
}