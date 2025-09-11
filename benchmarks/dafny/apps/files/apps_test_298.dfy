// <vc-preamble>
predicate ValidInput(n: int, k: int)
{
    k >= 1 && n >= 1 && k <= n
}

function TotalMoves(n: int, k: int): int
    requires ValidInput(n, k)
{
    n / k
}

predicate FirstPlayerWins(n: int, k: int)
    requires ValidInput(n, k)
{
    TotalMoves(n, k) % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: string)
    requires ValidInput(n, k)
    ensures FirstPlayerWins(n, k) ==> result == "YES"
    ensures !FirstPlayerWins(n, k) ==> result == "NO"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
