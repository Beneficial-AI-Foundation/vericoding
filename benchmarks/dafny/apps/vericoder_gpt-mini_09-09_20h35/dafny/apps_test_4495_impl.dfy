predicate ValidInput(a: int, b: int, x: int)
{
    a >= 0 && b >= a && x > 0
}

function CountDivisibleInRange(a: int, b: int, x: int): int
    requires ValidInput(a, b, x)
    ensures CountDivisibleInRange(a, b, x) >= 0
{
    if a == 0 then
        b / x + 1
    else
        b / x - (a - 1) / x
}

// <vc-helpers>
lemma DivMonotoneNonneg(p: int, q: int, x: int)
  requires x > 0 && 0 <= p && 0 <= q && p <= q
  ensures p / x <= q / x
{
  var qDiv := q / x;
  var qRem := q % x;
  assert q == x * qDiv + qRem;
  assert 0 <= qRem < x;

  if p / x > qDiv {
    // Then p / x >= qDiv + 1
    assert p / x >= qDiv + 1;

    // Standard properties of integer division:
    assert (p / x) * x <= p;
    assert p < (p / x + 1) * x;

    // From p / x >= qDiv + 1 we get x * (qDiv + 1) <= p
    assert x * (qDiv + 1) <= p;

    // But q = x * qDiv + qRem and qRem < x, so x * qDiv + qRem < x * (qDiv + 1)
    assert x * qDiv + qRem < x * (qDiv + 1);

    // Since p <= q = x*qDiv + qRem, we get p < x*(qDiv+1), contradicting x*(qDiv+1) <= p
    assert p <= x * qDiv + qRem;
    assert p < x * (qDiv + 1);
    // contradiction
    assert false;
  }
}

lemma CountDivisibleNonneg(a: int, b: int, x: int)
  requires ValidInput(a, b, x)
  ensures CountDivisibleInRange(a, b, x) >= 0
{
  if a == 0 {
    // CountDivisibleInRange(a,b,x) == b/x + 1 and b >= 0, x > 0
    assert b / x >= 0;
    assert b / x + 1 >= 0;
  } else {
    // a > 0, so a - 1 >= 0 and a - 1 <= b
    DivMonotoneNonneg(a - 1, b, x);
    // From lemma we have (a-1)/x <= b/x, hence difference >= 0
    assert b / x - (a - 1) / x >= 0;
  }
}
// </vc-helpers>

// <vc-spec>
method CountDivisible(a: int, b: int, x: int) returns (count: int)
    requires ValidInput(a, b, x)
    ensures count == CountDivisibleInRange(a, b, x)
    ensures count >= 0
// </vc-spec>
// <vc-code>
{
  if a == 0 {
    count := b / x + 1;
    // relate to specification and prove nonnegativity
    assert count == CountDivisibleInRange(a, b, x);
    assert count >= 0;
  } else {
    // Prove nonnegativity first
    CountDivisibleNonneg(a, b, x);
    var tmp := b / x - (a - 1) / x;
    count := tmp;
    // relate to specification and prove nonnegativity
    assert count == CountDivisibleInRange(a, b, x);
    assert count >= 0;
  }
}
// </vc-code>

