//IMPL
function SumArray(a: array<int>, start: int, end: int): int
requires 0 <= start <= end <= a.Length
reads a
{
    if start == end then 0
    else a[start] + SumArray(a, start + 1, end)
}

/* code modified by LLM (iteration 4): fixed lemma proof structure to properly establish additivity property */
lemma SumArrayExtend(a: array<int>, start: int, mid: int, end: int)
requires 0 <= start <= mid <= end <= a.Length
ensures SumArray(a, start, end) == SumArray(a, start, mid) + SumArray(a, mid, end)
{
    if start == mid {
        // Base case: SumArray(a, start, mid) == 0
        assert SumArray(a, start, mid) == 0;
        assert SumArray(a, start, end) == SumArray(a, mid, end);
    } else {
        // Inductive case: use recursion
        /* code modified by LLM (iteration 4): proper recursive proof with correct inductive step */
        SumArrayExtend(a, start + 1, mid, end);
        // Now we have: SumArray(a, start + 1, end) == SumArray(a, start + 1, mid) + SumArray(a, mid, end)
        
        // We need to show: SumArray(a, start, end) == SumArray(a, start, mid) + SumArray(a, mid, end)
        calc {
            SumArray(a, start, end);
        ==  // by definition of SumArray
            a[start] + SumArray(a, start + 1, end);
        ==  // by inductive hypothesis
            a[start] + SumArray(a, start + 1, mid) + SumArray(a, mid, end);
        ==  // by definition of SumArray
            SumArray(a, start, mid) + SumArray(a, mid, end);
        }
    }
}

method Sum(a: array<int>) returns (res: int)
ensures res == SumArray(a, 0, a.Length)
{
    res := 0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant res == SumArray(a, 0, i)
    {
        /* code modified by LLM (iteration 4): use lemma to prove invariant maintenance with proper bounds */
        assert SumArray(a, 0, i + 1) == SumArray(a, 0, i) + SumArray(a, i, i + 1);
        SumArrayExtend(a, 0, i, i + 1);
        assert SumArray(a, i, i + 1) == a[i];
        res := res + a[i];
        i := i + 1;
    }
}