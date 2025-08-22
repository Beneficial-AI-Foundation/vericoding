//IMPL
function ProdArray(a: array<int>, start: int, end: int): int
requires 0 <= start <= end <= a.Length
{
    if start == end then 1
    else a[start] * ProdArray(a, start + 1, end)
}

/* code modified by LLM (iteration 3): fixed lemma logic to properly establish the relationship */
lemma ProdArrayExtend(a: array<int>, start: int, end: int)
requires 0 <= start < end <= a.Length
ensures ProdArray(a, start, end) == ProdArray(a, start, end - 1) * a[end - 1]
{
    if start == end - 1 {
        // Base case: ProdArray(a, start, end) = a[start] and ProdArray(a, start, end-1) = 1
        // So we need a[start] == 1 * a[end-1], which is true since start == end-1
        assert ProdArray(a, start, end - 1) == 1;
        assert ProdArray(a, start, end) == a[start];
        assert a[start] == a[end - 1]; // since start == end - 1
    } else {
        // Recursive case: use induction
        ProdArrayExtend(a, start + 1, end);
        // Now we know ProdArray(a, start+1, end) == ProdArray(a, start+1, end-1) * a[end-1]
        // And ProdArray(a, start, end) == a[start] * ProdArray(a, start+1, end)
        // And ProdArray(a, start, end-1) == a[start] * ProdArray(a, start+1, end-1)
    }
}

method Prod(a: array<int>) returns (res: int)
ensures res == ProdArray(a, 0, a.Length)
{
    res := 1;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant res == ProdArray(a, 0, i)
    {
        /* code modified by LLM (iteration 3): call lemma to establish relationship before update */
        ProdArrayExtend(a, 0, i + 1);
        res := res * a[i];
        i := i + 1;
    }
}