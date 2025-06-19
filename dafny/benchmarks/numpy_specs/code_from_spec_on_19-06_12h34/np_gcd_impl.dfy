//ATOM
/* code modified by LLM (iteration 1): Added decreases clause for termination and improved GCD algorithm */
function GCDInt(a: int, b: int): int
requires a >= 0 && b >= 0
decreases b
{
    if b == 0 then a
    else GCDInt(b, a % b)
}

//IMPL
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
    invariant forall j :: 0 <= j < i ==> res[j] == GCDInt(a[j], b[j])
    {
        /* code modified by LLM (iteration 1): Direct assignment of GCD computation result */
        res[i] := GCDInt(a[i], b[i]);
        i := i + 1;
    }
}