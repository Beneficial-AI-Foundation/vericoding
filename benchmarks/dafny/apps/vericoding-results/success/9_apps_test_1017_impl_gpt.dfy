predicate ValidInput(n: int) {
    n >= 1
}

function MaxDistributions(n: int): int
    requires ValidInput(n)
{
    if n % 3 == 0 then 2 * (n / 3) else 2 * (n / 3) + 1
}

// <vc-helpers>
lemma MaxDistributionsLowerBound(n: int)
  requires ValidInput(n)
  ensures MaxDistributions(n) >= 1
{
  if n % 3 == 0 {
    assert n / 3 >= 0;
    assert n == 3 * (n / 3) + n % 3;
    assert n == 3 * (n / 3);
    if n / 3 == 0 {
      assert n == 3 * 0;
      assert n == 0;
      assert false;
    }
    assert n / 3 >= 1;
    assert MaxDistributions(n) == 2 * (n / 3);
    assert MaxDistributions(n) >= 2;
  } else {
    assert n / 3 >= 0;
    assert MaxDistributions(n) == 2 * (n / 3) + 1;
    assert MaxDistributions(n) >= 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures result == MaxDistributions(n)
// </vc-spec>
// <vc-code>
{
  MaxDistributionsLowerBound(n);
  result := MaxDistributions(n);
  assert result >= 1;
}
// </vc-code>

