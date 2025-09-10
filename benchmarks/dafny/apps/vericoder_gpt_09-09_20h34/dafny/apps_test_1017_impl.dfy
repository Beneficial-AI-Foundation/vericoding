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
    var k := n / 3;
    assert n == 3 * k + n % 3;
    assert n == 3 * k;
    if k <= 0 {
      assert 3 * k <= 0;
      assert n <= 0;
      assert false;
    }
    assert k >= 1;
    assert 2 * k >= 2;
    assert MaxDistributions(n) == 2 * k;
  } else {
    var k := n / 3;
    var r := n % 3;
    assert 0 <= r && r < 3;
    assert r != 0;
    assert r >= 1;
    assert r <= 2;
    assert n == 3 * k + r;
    if k < 0 {
      assert k <= -1;
      assert 3 * k <= -3;
      assert 3 * k + r <= -3 + r;
      assert -3 + r <= -1;
      assert n <= -1;
      assert false;
    }
    assert k >= 0;
    assert 2 * k + 1 >= 1;
    assert MaxDistributions(n) == 2 * k + 1;
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
  result := MaxDistributions(n);
  MaxDistributionsLowerBound(n);
}
// </vc-code>

