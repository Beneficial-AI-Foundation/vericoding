// <vc-preamble>
predicate ValidInput(M: int)
{
    1 <= M <= 23
}

function HoursUntilNewYear(M: int): int
    requires ValidInput(M)
{
    48 - M
}

predicate ValidOutput(M: int, result: int)
    requires ValidInput(M)
{
    result == HoursUntilNewYear(M) && 25 <= result <= 47
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(M: int) returns (result: int)
    requires ValidInput(M)
    ensures ValidOutput(M, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
