//IMPL
method RightShift(a: array<int>, b: array<nat>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < b.Length ==> b[i] < 64
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] >> b[i]
{
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant res.Length == a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == a[j] >> b[j]
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        decreases a.Length - i
    {
        res[i] := a[i] >> b[i];
        i := i + 1;
    }
}