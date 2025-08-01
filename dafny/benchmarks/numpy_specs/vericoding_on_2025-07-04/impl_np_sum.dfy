//ATOM
function SumArray(a: array<int>, start: int, end: int): int
requires 0 <= start <= end <= a.Length
reads a
decreases end - start
{
    if start == end then 0 else a[start] + SumArray(a, start + 1, end)
}

//IMPL
method Sum(a: array<int>) returns (res: int)
ensures res == SumArray(a, 0, a.Length)
{
    res := 0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant res == SumArray(a, 0, i)
    {
        /* code modified by LLM (iteration 1): Fixed assertions to correctly decompose SumArray by showing that SumArray(a, 0, i+1) = SumArray(a, 0, i) + a[i] */
        assert SumArray(a, 0, i + 1) == SumArray(a, 0, i) + SumArray(a, i, i + 1);
        assert SumArray(a, i, i + 1) == a[i] + SumArray(a, i + 1, i + 1);
        assert SumArray(a, i + 1, i + 1) == 0;
        assert SumArray(a, 0, i + 1) == SumArray(a, 0, i) + a[i];
        
        res := res + a[i];
        i := i + 1;
    }
}