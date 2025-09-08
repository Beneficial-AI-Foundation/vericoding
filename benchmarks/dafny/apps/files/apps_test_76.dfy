Given n commentary boxes and m delegations, make the number of boxes divisible by m at minimum cost.
You can build a box for cost a or demolish a box for cost b.
Find the minimum cost to make n divisible by m.

predicate ValidInput(n: int, m: int, a: int, b: int)
{
    n >= 1 && m >= 1 && a >= 1 && b >= 1
}

function MinCostToDivisible(n: int, m: int, a: int, b: int): int
    requires ValidInput(n, m, a, b)
{
    var k := n % m;
    if k * b < (m - k) * a then k * b else (m - k) * a
}

method solve(n: int, m: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, m, a, b)
    ensures result == MinCostToDivisible(n, m, a, b)
    ensures result >= 0
{
    var k := n % m;
    result := if k * b < (m - k) * a then k * b else (m - k) * a;
}
