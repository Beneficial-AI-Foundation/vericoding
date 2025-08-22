//IMPL

/* code modified by LLM (iteration 4): Added recursive function body for ProdArray */
function ProdArray(a: array<int>, start: int, end: int): int
requires 0 <= start <= end <= a.Length
reads a
{
    if start == end then 1
    else a[start] * ProdArray(a, start + 1, end)
}

/* code modified by LLM (iteration 4): Added lemma to help prove the relationship between consecutive ProdArray calls */
lemma ProdArrayExtend(a: array<int>, start: int, end: int)
requires 0 <= start < end <= a.Length
ensures ProdArray(a, start, end) == a[start] * ProdArray(a, start + 1, end)
{
    // This follows directly from the definition of ProdArray
}

/* code modified by LLM (iteration 4): Modified method with correct lemma application and proof structure */
method Prod(a: array<int>) returns (res: int)
ensures res == ProdArray(a, 0, a.Length)
{
    res := 1;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant res == ProdArray(a, 0, i)
    {
        /* code modified by LLM (iteration 4): Added correct lemma call to prove invariant maintenance */
        if i + 1 <= a.Length {
            ProdArrayExtend(a, 0, i + 1);
        }
        res := res * a[i];
        i := i + 1;
    }
}