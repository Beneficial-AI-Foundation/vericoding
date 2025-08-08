//IMPL

/* code modified by LLM (iteration 3): Added decreases clause for termination and fixed recursive structure */
function ProdArray(a: array<int>, start: int, end: int): int
requires 0 <= start <= end <= a.Length
reads a
decreases end - start
{
    if start == end then 1
    else a[start] * ProdArray(a, start + 1, end)
}

/* code modified by LLM (iteration 3): Fixed lemma to properly prove the extension property */
lemma ProdArrayExtend(a: array<int>, start: int, mid: int, end: int)
requires 0 <= start <= mid < end <= a.Length
ensures ProdArray(a, start, end) == ProdArray(a, start, mid) * ProdArray(a, mid, end)
decreases end - start
{
    if start == mid {
        assert ProdArray(a, start, mid) == 1;
        assert ProdArray(a, start, end) == ProdArray(a, mid, end);
    } else {
        ProdArrayExtend(a, start + 1, mid, end);
        assert ProdArray(a, start, end) == a[start] * ProdArray(a, start + 1, end);
        assert ProdArray(a, start + 1, end) == ProdArray(a, start + 1, mid) * ProdArray(a, mid, end);
        assert ProdArray(a, start, mid) == a[start] * ProdArray(a, start + 1, mid);
    }
}

/* code modified by LLM (iteration 3): Added helper lemma to prove single step extension */
lemma ProdArraySingleStep(a: array<int>, start: int, end: int)
requires 0 <= start < end <= a.Length
ensures ProdArray(a, start, end) == ProdArray(a, start, end - 1) * a[end - 1]
decreases end - start
{
    if start == end - 1 {
        assert ProdArray(a, start, end - 1) == 1;
    } else {
        ProdArraySingleStep(a, start + 1, end);
    }
}

/* code modified by LLM (iteration 3): Fixed method with proper lemma calls for verification */
method Prod(a: array<int>) returns (res: int)
ensures res == ProdArray(a, 0, a.Length)
{
    res := 1;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant res == ProdArray(a, 0, i)
    {
        /* code modified by LLM (iteration 3): Use helper lemma to establish the step */
        ProdArraySingleStep(a, 0, i + 1);
        res := res * a[i];
        i := i + 1;
    }
}