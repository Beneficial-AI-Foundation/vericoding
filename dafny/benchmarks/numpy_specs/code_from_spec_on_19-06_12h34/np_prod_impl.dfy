//IMPL
method Prod(a: array<int>) returns (res: int)
ensures res == ProdArray(a, 0, a.Length)
{
    res := 1;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant res == ProdArray(a, 0, i)
    {
        /* code modified by LLM (iteration 2): call lemma with correct parameters before updating variables */
        ProdArrayLemma(a, 0, i);
        res := res * a[i];
        i := i + 1;
    }
}

function ProdArray(a: array<int>, start: int, end: int): int
requires 0 <= start <= end <= a.Length
{
    if start == end then 1
    else a[start] * ProdArray(a, start + 1, end)
}

/* code modified by LLM (iteration 2): corrected helper lemma to prove the exact relationship needed */
lemma ProdArrayLemma(a: array<int>, start: int, i: int)
requires 0 <= start <= i < a.Length
ensures ProdArray(a, start, i) * a[i] == ProdArray(a, start, i + 1)
{
    if start == i {
        // Base case: ProdArray(a, i, i) * a[i] == ProdArray(a, i, i+1)
        assert ProdArray(a, i, i) == 1;
        assert ProdArray(a, i, i + 1) == a[i] * ProdArray(a, i + 1, i + 1);
        assert ProdArray(a, i + 1, i + 1) == 1;
        assert ProdArray(a, i, i + 1) == a[i];
    } else {
        // Recursive case: use inductive hypothesis
        ProdArrayLemma(a, start + 1, i);
        assert ProdArray(a, start, i) == a[start] * ProdArray(a, start + 1, i);
        assert ProdArray(a, start + 1, i) * a[i] == ProdArray(a, start + 1, i + 1);
        assert ProdArray(a, start, i + 1) == a[start] * ProdArray(a, start + 1, i + 1);
    }
}