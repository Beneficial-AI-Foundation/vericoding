//IMPL

method Prod(a: array<int>) returns (res: int)
ensures res == ProdArray(a, 0, a.Length)
function ProdArray(a: array<int>, start: int, end: int): int
requires 0 <= start <= end <= a.Length
{
    res := 1;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant res == ProdArray(a, 0, i)
    {
        res := res * a[i];
        i := i + 1;
    }
}