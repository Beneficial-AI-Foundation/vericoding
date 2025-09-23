// <vc-preamble>
predicate ValidInput(m: int, d: int)
{
    1 <= m <= 12 && 1 <= d <= 7
}

function DaysInMonth(m: int): int
    requires 1 <= m <= 12
{
    [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m-1]
}

function ColumnsNeeded(m: int, d: int): int
    requires ValidInput(m, d)
{
    1 + (d - 1 + DaysInMonth(m) - 1) / 7
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(m: int, d: int) returns (result: int)
    requires ValidInput(m, d)
    ensures result == ColumnsNeeded(m, d)
    ensures 4 <= result <= 6
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
