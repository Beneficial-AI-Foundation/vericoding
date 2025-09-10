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
lemma FloorDivMonotonic(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  ensures FloorDiv(x, k) <= FloorDiv(y, k)
{
  if x >= 0 && y >= 0 {
    // Both non-negative: x/k <= y/k follows from x <= y
    assert x / k <= y / k;
  } else if x < 0 && y < 0 {
    // Both negative: need to show (x - k + 1) / k <= (y - k + 1) / k
    assert (x - k + 1) <= (y - k + 1);
    assert (x - k + 1) / k <= (y - k + 1) / k;
  } else {
    // x < 0 <= y
    assert x < 0 && y >= 0;
    // FloorDiv(x, k) = (x - k + 1) / k < 0
    // FloorDiv(y, k) = y / k >= 0
    assert (x - k + 1) < 0;
    assert (x - k + 1) / k < 0;
    assert y / k >= 0;
    assert FloorDiv(x, k) < 0 <= FloorDiv(y, k);
  }
}

lemma CountDivisiblesNonNegative(k: int, a: int, b: int)
  requires k > 0
  requires a <= b
  ensures CountDivisiblesInRange(k, a, b) >= 0
{
  assert a - 1 < a <= b;
  FloorDivMonotonic(a - 1, b, k);
  assert FloorDiv(a - 1, k) <= FloorDiv(b, k);
  assert CountDivisiblesInRange(k, a, b) == FloorDiv(b, k) - FloorDiv(a - 1, k);
  assert CountDivisiblesInRange(k, a, b) >= 0;
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
  CountDivisiblesNonNegative(k, a, b);
  var countUpToB := if b >= 0 then b / k else (b - k + 1) / k;
  var countUpToAMinus1 := if a - 1 >= 0 then (a - 1) / k else ((a - 1) - k + 1) / k;
  result := countUpToB - countUpToAMinus1;
}
// </vc-code>

