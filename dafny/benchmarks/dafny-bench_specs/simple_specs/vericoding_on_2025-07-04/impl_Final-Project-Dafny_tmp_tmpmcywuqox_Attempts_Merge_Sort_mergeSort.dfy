//ATOM

method merging(a: array<int>, low: int, medium: int, high: int)
requires 0 <= low <= medium <= high < a.Length
modifies a
{
}


//ATOM

method sorting(a: array<int>, low: int, high: int)
requires 0 <= low && high < a.Length
modifies a
{
}


//IMPL mergeSort
method mergeSort(a: array<int>)
modifies a
{
    if a.Length > 1 {
        /* code modified by LLM (iteration 2): added explicit assertions to verify each part of the precondition */
        assert 0 <= 0;
        assert a.Length - 1 < a.Length;
        assert 0 <= 0 && a.Length - 1 < a.Length;
        sorting(a, 0, a.Length - 1);
    }
}