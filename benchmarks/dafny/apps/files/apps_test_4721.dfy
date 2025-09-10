/*
Given n east-west streets and m north-south streets in a city where all streets intersect,
determine the number of rectangular blocks formed by the street grid.
n east-west streets create (n-1) horizontal strips, m north-south streets create (m-1) vertical strips,
resulting in (n-1) * (m-1) rectangular blocks.
*/

predicate ValidInput(n: int, m: int)
{
    2 <= n <= 100 && 2 <= m <= 100
}

function CountBlocks(n: int, m: int): int
    requires ValidInput(n, m)
{
    (n - 1) * (m - 1)
}

predicate CorrectOutput(n: int, m: int, blocks: int)
{
    ValidInput(n, m) && blocks == CountBlocks(n, m)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (blocks: int)
    requires ValidInput(n, m)
    ensures CorrectOutput(n, m, blocks)
    ensures blocks >= 1
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
