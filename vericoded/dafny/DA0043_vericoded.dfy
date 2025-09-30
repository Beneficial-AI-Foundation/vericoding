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
lemma DivMonotonicPositive(x: int, y: int, k: int)
  requires k > 0
  requires 0 <= x <= y
  ensures x / k <= y / k
{
  // We need to prove that x/k <= y/k when 0 <= x <= y and k > 0
  // This follows from the fact that integer division is monotonic for non-negative dividends
  var qx := x / k;
  var qy := y / k;
  var rx := x % k;
  var ry := y % k;
  
  assert x == qx * k + rx && 0 <= rx < k;
  assert y == qy * k + ry && 0 <= ry < k;
  
  if qx > qy {
    // If qx > qy, then qx >= qy + 1
    assert qx >= qy + 1;
    assert x == qx * k + rx >= (qy + 1) * k + 0;
    assert x >= qy * k + k;
    assert x >= y - ry + k;
    assert x >= y + (k - ry);
    assert x > y;  // Since k - ry > 0
    assert false;  // Contradiction with x <= y
  }
  assert qx <= qy;
}

lemma DivMonotonicNegative(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  requires x < 0
  requires y < 0
  ensures (x - k + 1) / k <= (y - k + 1) / k
{
  // Since x <= y, we have x - k + 1 <= y - k + 1
  assert (x - k + 1) <= (y - k + 1);
  
  // Both (x - k + 1) and (y - k + 1) are negative since x < 0 and y < 0
  assert x - k + 1 < 0;
  assert y - k + 1 < 0;
  
  // For negative numbers, we need to show division is monotonic
  var a := x - k + 1;
  var b := y - k + 1;
  assert a <= b;
  assert a < 0 && b < 0;
  
  var qa := a / k;
  var qb := b / k;
  
  if qa > qb {
    // If qa > qb, then qa >= qb + 1
    assert qa >= qb + 1;
    // Since a < 0, qa <= -1, so qb <= qa - 1 <= -2
    assert a >= qa * k;  // Division property for negative numbers
    assert b < (qb + 1) * k;  // Division property for negative numbers
    assert a >= qa * k >= (qb + 1) * k > b;
    assert a > b;
    assert false;  // Contradiction with a <= b
  }
  assert qa <= qb;
}

lemma FloorDivMonotonic(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  ensures FloorDiv(x, k) <= FloorDiv(y, k)
{
  if x >= 0 {
    assert y >= 0;  // Since x <= y and x >= 0
    DivMonotonicPositive(x, y, k);
    assert FloorDiv(x, k) == x / k;
    assert FloorDiv(y, k) == y / k;
  } else if y < 0 {
    // Both negative
    DivMonotonicNegative(x, y, k);
    assert FloorDiv(x, k) == (x - k + 1) / k;
    assert FloorDiv(y, k) == (y - k + 1) / k;
  } else {
    // x < 0 <= y
    assert FloorDiv(x, k) == (x - k + 1) / k;
    assert FloorDiv(y, k) == y / k;
    assert x - k + 1 <= x < 0;
    assert (x - k + 1) / k <= 0;
    assert 0 <= y / k;
  }
}

lemma CountDivisiblesNonNegative(k: int, a: int, b: int)
  requires k > 0
  requires a <= b
  ensures CountDivisiblesInRange(k, a, b) >= 0
{
  FloorDivMonotonic(a - 1, b, k);
  assert FloorDiv(a - 1, k) <= FloorDiv(b, k);
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

