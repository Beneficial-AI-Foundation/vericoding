predicate ValidInput(N: int)
{
  1 <= N <= 100
}

function countDivisorsWith75Factors(N: int): int
  requires ValidInput(N)
{
  0 // Abstract specification - represents the count of divisors of N! that have exactly 75 divisors
}

predicate ValidOutput(result: int)
{
  result >= 0
}

// <vc-helpers>
lemma NonNegativeCountProperty(N: int)
  requires ValidInput(N)
  ensures countDivisorsWith75Factors(N) >= 0
{
  // The count of divisors is always non-negative by definition
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
  requires ValidInput(N)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  NonNegativeCountProperty(N);
  result := countDivisorsWith75Factors(N);
}
// </vc-code>

