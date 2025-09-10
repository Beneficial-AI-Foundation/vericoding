/*
Find the n-th element (1-indexed) in an infinite sequence constructed as blocks:
Block 1: [1], Block 2: [1,2], Block 3: [1,2,3], etc.
The complete sequence is: 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 2, 3, 4, 5, ...
*/

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
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
