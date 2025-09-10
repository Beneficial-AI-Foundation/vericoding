predicate ValidInput(n: int) {
    n >= 1
}

function WorstCasePresses(n: int): int
    requires ValidInput(n)
{
    n * (n * n + 5) / 6
}

// <vc-helpers>
lemma WorstCasePressesLowerBound(n: int)
  requires ValidInput(n)
  ensures WorstCasePresses(n) >= 1
{
  // Factorization: n*(n*n + 5) - 6 == (n - 1)*(n*n + n + 6)
  assert n*(n*n + 5) - 6 == (n - 1)*(n*n + n + 6);

  assert n - 1 >= 0;
  assert n*n + n + 6 >= 0;

  // Therefore the left-hand side is non-negative
  assert (n - 1)*(n*n + n + 6) >= 0;
  assert n*(n*n + 5) - 6 >= 0;

  // Hence the numerator is at least 6
  assert n*(n*n + 5) >= 6;

  // Divide by positive 6 to get the bound on the quotient
  assert WorstCasePresses(n) == n*(n*n + 5) / 6;
  assert WorstCasePresses(n) >= 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == WorstCasePresses(n)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
  result := WorstCasePresses(n);
  WorstCasePressesLowerBound(n);
}
// </vc-code>

