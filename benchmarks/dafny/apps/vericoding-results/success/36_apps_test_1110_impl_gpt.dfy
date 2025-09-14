predicate ValidInput(n: int) {
    n >= 1
}

function WorstCasePresses(n: int): int
    requires ValidInput(n)
{
    n * (n * n + 5) / 6
}

// <vc-helpers>

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
  assert n >= 1;
  assert n >= 0;
  assert n - 1 >= 0;
  assert n * (n*n + 5) == 6 + (n - 1) * (n*n + n + 6);
  assert n*n >= 0;
  assert n*n + n + 6 >= 0;
  assert (n - 1) * (n*n + n + 6) >= 0;
  assert n * (n*n + 5) >= 6;
  assert 6 > 0;
  assert result == n * (n*n + 5) / 6;
  assert result >= 6 / 6;
  assert 6 / 6 == 1;
}
// </vc-code>

