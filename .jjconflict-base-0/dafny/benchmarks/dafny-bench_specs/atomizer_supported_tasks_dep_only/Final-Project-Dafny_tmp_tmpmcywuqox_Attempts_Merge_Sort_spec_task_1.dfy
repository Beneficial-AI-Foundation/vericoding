// SPEC 
method mergeSort(a: array<int>)
modifies a
{
}


// SPEC 

method merging(a: array<int>, low: int, medium: int, high: int)
requires 0 <= low <= medium <= high < a.Length
modifies a
{
}


// SPEC 

method sorting(a: array<int>, low: int, high: int)
requires 0 <= low && high < a.Length
modifies a
{
}


