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
        sorting(a, 0, a.Length - 1);
    }
}