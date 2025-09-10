predicate ValidInput(k: int, a: int, b: int)
{
  k > 0 && a <= b
}

function FloorDiv(a: int, b: int): int
  requires b > 0
{
  if a >= 0 then a / b
  else (a - b + 1) / b
}

function CountDivisiblesInRange(k: int, a: int, b: int): int
  requires k > 0
  requires a <= b
{
  FloorDiv(b, k) - FloorDiv(a - 1, k)
}

// <vc-helpers>
lemma FloorDivLemma(a: int, b: int)
  requires b > 0
  ensures FloorDiv(a, b) * b <= a < (FloorDiv(a, b) + 1) * b
{
  if a >= 0 {
    assert a / b * b <= a < (a / b + 1) * b;
  } else {
    var q := (a - b + 1) / b;
    assert q * b <= a - b + 1;
    assert a < (q + 1) * b;
    assert q * b <= a - b + 1 && a - b + 1 < (q + 1) * b;
  }
}

lemma CountDivisiblesInRangeLemma(k: int, a: int, b: int, x: int)
  requires k > 0 && a <= b
  requires a <= x <= b
  requires k * (FloorDiv(a - 1, k) + 1) <= x <= k * FloorDiv(b, k)
  ensures x % k == 0
{
  FloorDivLemma(x, k);
  var qx := FloorDiv(x, k);
  assert qx * k <= x < (qx + 1) * k;
  
  var qa := FloorDiv(a - 1, k);
  assert qa * k <= a - 1 < (qa + 1) * k;
  
  var qb := FloorDiv(b, k);
  assert qb * k <= b < (qb + 1) * k;
  
  assert qa + 1 <= qx <= qb;
  assert x >= qx * k;
  assert x < (qx + 1) * k;
  assert x >= (qa + 1) * k;
  assert x <= qb * k;
  assert x % k == 0;
}

lemma FloorDivRangeLemma(a: int, b: int, k: int)
  requires k > 0
  ensures FloorDiv(a - 1, k) <= FloorDiv(b, k)
{
  if a - 1 <= b {
    assert FloorDiv(a - 1, k) <= FloorDiv(b, k);
  } else {
    // This case should not occur since a <= b implies a-1 <= b
    assert false;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, a: int, b: int) returns (result: int)
  requires ValidInput(k, a, b)
  ensures result >= 0
  ensures result == CountDivisiblesInRange(k, a, b)
// </vc-spec>
// <vc-code>
{
  result := FloorDiv(b, k) - FloorDiv(a - 1, k);
  if CountDivisiblesInRange(k, a, b) == 0 {
    assert result == 0;
  }
  assert result >= 0;
}
// </vc-code>

