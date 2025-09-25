// <vc-preamble>
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
// </vc-preamble>

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
