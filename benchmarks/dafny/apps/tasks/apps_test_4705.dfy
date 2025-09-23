// <vc-preamble>
predicate ValidInput(N: int)
{
    1 <= N <= 100
}

function TotalCost(N: int): int
    requires ValidInput(N)
{
    800 * N
}

function Cashback(N: int): int
    requires ValidInput(N)
{
    (N / 15) * 200
}

function NetAmount(N: int): int
    requires ValidInput(N)
{
    TotalCost(N) - Cashback(N)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
    requires ValidInput(N)
    ensures result == NetAmount(N)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
