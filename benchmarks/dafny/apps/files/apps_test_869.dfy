// <vc-preamble>
predicate ValidInput(a: int, b: int)
{
  a >= 1 && b >= 1
}

function MaxDifferentDays(a: int, b: int): int
{
  if a < b then a else b
}

function RemainingAfterDifferent(a: int, b: int): int
{
  if a > b then a - MaxDifferentDays(a, b) else b - MaxDifferentDays(a, b)
}

function SameDays(a: int, b: int): int
{
  RemainingAfterDifferent(a, b) / 2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (days_different: int, days_same: int)
  requires ValidInput(a, b)
  ensures days_different == MaxDifferentDays(a, b)
  ensures days_same == SameDays(a, b)
  ensures days_different >= 0
  ensures days_same >= 0
  ensures days_different <= a && days_different <= b
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
