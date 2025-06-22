//IMPL
/* code modified by LLM (iteration 4): moved ProdArray function to top level - functions cannot be defined inside methods */
function ProdArray(a: array<int>, start: int, end: int): int
requires 0 <= start <= end <= a.Length
reads a
{
    if start == end then 1
    else a[start] * ProdArray(a, start + 1, end)
}

/* code modified by LLM (iteration 4): added helper lemma to prove relationship between consecutive ProdArray calls */
lemma ProdArrayLemma(a: array<int>, start: int, end: int)
requires 0 <= start < end <= a.Length
ensures ProdArray(a, start, end) == a[start] * ProdArray(a, start + 1, end)
{
    // This follows directly from the definition of ProdArray
}

method Prod(a: array<int>) returns (res: int)
ensures res == ProdArray(a, 0, a.Length)
{
    /* code modified by LLM (iteration 4): fixed method implementation with correct proof logic */
    res := 1;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant res == ProdArray(a, 0, i)
    {
        /* code modified by LLM (iteration 4): restructured proof to show invariant maintenance correctly */
        // Before update: res == ProdArray(a, 0, i)
        // After update: res * a[i] == ProdArray(a, 0, i+1)
        // We need to show: ProdArray(a, 0, i+1) == ProdArray(a, 0, i) * a[i]
        
        if i < a.Length {
            // Apply the lemma to show the relationship
            ProdArrayLemma(a, 0, i + 1);
        }
        
        res := res * a[i];
        i := i + 1;
    }
}