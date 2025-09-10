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
  // Dafny can verify this automatically
}

lemma DivMonotonicNegative(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  requires x < 0
  requires y < 0
  ensures (x - k + 1) / k <= (y - k + 1) / k
{
  assert (x - k + 1) <= (y - k + 1);
  // Dafny can verify this automatically
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

