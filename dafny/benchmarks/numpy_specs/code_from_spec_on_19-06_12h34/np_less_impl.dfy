//IMPL
method Less(a: array<int>, b: array<int>) returns (res: array<bool>)
requires a.Length == b.Length
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] < b[i])
{
    res := new bool[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == (a[j] < b[j])
    {
        /* code modified by LLM (iteration 1): fixed variable name from b[j] to b[i] */
        res[i] := a[i] < b[i];
        i := i + 1;
    }
}