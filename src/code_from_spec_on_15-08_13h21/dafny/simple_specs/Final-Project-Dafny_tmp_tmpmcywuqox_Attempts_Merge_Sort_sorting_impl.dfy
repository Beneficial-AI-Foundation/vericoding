method merging(a: array<int>, low: int, medium: int, high: int)
requires 0 <= low <= medium <= high < a.Length
modifies a
{
}


//IMPL sorting

method sorting(a: array<int>, low: int, high: int)
requires 0 <= low && high < a.Length
modifies a
/* code modified by LLM (iteration 1): added decreases clause to prove termination */
decreases high - low
{
    if low < high {
        var medium := (low + high) / 2;
        sorting(a, low, medium);
        sorting(a, medium + 1, high);
        merging(a, low, medium, high);
    }
}