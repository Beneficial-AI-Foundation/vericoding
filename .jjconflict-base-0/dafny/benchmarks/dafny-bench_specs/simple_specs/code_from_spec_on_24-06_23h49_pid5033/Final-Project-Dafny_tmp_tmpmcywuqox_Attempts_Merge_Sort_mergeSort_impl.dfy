//ATOM merging
method merging(a: array<int>, low: int, medium: int, high: int)
requires 0 <= low <= medium <= high < a.Length
modifies a
{
}

//ATOM sorting
method sorting(a: array<int>, low: int, high: int)
requires 0 <= low && high < a.Length
modifies a
{
}

//IMPL mergeSort
method mergeSort(a: array<int>)
modifies a
{
    /* code modified by LLM (iteration 1): Added bounds check to ensure preconditions of sorting method are satisfied */
    if a.Length > 1 {
        sorting(a, 0, a.Length - 1);
    }
}