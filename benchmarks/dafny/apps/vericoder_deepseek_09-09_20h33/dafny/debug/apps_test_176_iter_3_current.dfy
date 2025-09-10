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
    assert (a - b + 1) / b * b <= a - b + 1 < ((a - b + 1) / b + 1) * b;
    assert FloorDiv(a, b) == (a - b + 1) / b;
    assert FloorDiv(a, b) * b <= a < (FloorDiv(a, b) + 1) * b;
  }
}

lemma CountDivisiblesInRangeLemma(k: int, a: int, b: int, x: int)
  requires k > 0 && a <= b
  requires a <= x <= b
  requires k * (FloorDiv(a - 1, k) + 1) <= x <= k * FloorDiv(b, k)
  ensures x % k == 0
{
  FloorDivLemma(x, k);
  FloorDivLemma(a - 1, k);
  FloorDivLemma(b, k);
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
}
// </vc-code>

