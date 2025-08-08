//ATOM
function SumArray(a: array<int>, start: int, end: int): int
requires 0 <= start <= end <= a.Length
reads a
decreases end - start
{
    if start == end then 0 else a[start] + SumArray(a, start + 1, end)
}

//SPEC
method Sum(a: array<int>) returns (res: int)
ensures res == SumArray(a, 0, a.Length)
{}
