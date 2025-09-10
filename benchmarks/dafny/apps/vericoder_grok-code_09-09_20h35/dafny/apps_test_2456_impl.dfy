predicate ValidInput(n: int, r: int)
{
    n >= 1 && r >= 1
}

function ExpectedResult(n: int, r: int): int
    requires ValidInput(n, r)
{
    var k := if r < n - 1 then r else n - 1;
    k * (k + 1) / 2 + (if r >= n then 1 else 0)
}

// <vc-helpers>
lemma DivisibilityLemma(k: int)
  requires k >= 0
  ensures k * (k + 1) % 2 == 0
{
  if k % 2 == 0 {
    assert k * (k + 1) % 2 == 0;
  } else {
    assert k % 2 != 0;
    assert (k + 1) % 2 == 0;
    assert k * (k + 1) % 2 == 0;
  }
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var k := if r < n - 1 then r else n - 1;
  assert k >= 0;
  DivisibilityLemma(k);
  return k * (k + 1) / 2 + (if r >= n then 1 else 0);
}
// </vc-code>

