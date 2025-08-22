//ATOM
function SumArray(a: array<int>, start: int, end: int): int
requires 0 <= start <= end <= a.Length
reads a
decreases end - start
{
    if start == end then 0 else a[start] + SumArray(a, start + 1, end)
}

/* code modified by LLM (iteration 3): Added helper lemma to prove SumArray extension property */
lemma SumArrayExtension(a: array<int>, start: int, end: int)
requires 0 <= start < end <= a.Length
ensures SumArray(a, start, end) == SumArray(a, start, end - 1) + a[end - 1]
{
    if start == end - 1 {
        assert SumArray(a, start, end - 1) == 0;
        assert SumArray(a, start, end) == a[start];
    } else {
        SumArrayExtension(a, start + 1, end);
        assert SumArray(a, start, end) == a[start] + SumArray(a, start + 1, end);
        assert SumArray(a, start + 1, end) == SumArray(a, start + 1, end - 1) + a[end - 1];
        assert SumArray(a, start, end - 1) == a[start] + SumArray(a, start + 1, end - 1);
    }
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
        /* code modified by LLM (iteration 3): Fixed lemma call to use correct parameters after increment */
        res := res + a[i];
        i := i + 1;
        
        if i > 0 {
            SumArrayExtension(a, 0, i);
        }
    }
}