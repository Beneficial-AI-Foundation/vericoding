//SPEC
method Prod(a: array<int>) returns (res: int)
ensures res == ProdArray(a, 0, a.Length)
function ProdArray(a: array<int>, start: int, end: int): int
requires 0 <= start <= end <= a.Length
{}