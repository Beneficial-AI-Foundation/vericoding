function TriangularNumber(m: int): int
    requires m >= 0
{
    m * (m + 1) / 2
}

predicate ValidInput(n: int)
{
    n >= 1
}

predicate ValidResult(n: int, result: int)
    requires ValidInput(n)
{
    result >= 1 && result <= n
}

// <vc-helpers>
function findK(n: int): int
    requires n >= 1
    ensures 1 <= findK(n) <= n
    ensures n >= (findK(n) * (findK(n) + 1)) / 2
    ensures n < ((findK(n) + 1) * (findK(n) + 2)) / 2
{
    var k := 1;
    while ((k * (k + 1)) / 2) <= n
        invariant k >= 1
        invariant forall x :: 0 <= x < k ==> ((x * (x + 1)) / 2) <= n // This ensures that TriangularNumber(k-1) <= n
    {
        k := k + 1;
    }
    return k - 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
    var k := findK(n);
    result := k;
}
// </vc-code>

