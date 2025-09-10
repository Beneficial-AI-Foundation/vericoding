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
lemma FloorDiv_monotone(k: int, x: int, y: int)
  requires k > 0
  requires x <= y
  ensures FloorDiv(x, k) <= FloorDiv(y, k)
{
  if x >= 0 {
    // then y >= 0 as well because x <= y
    calc {
      y;
      >= x;
      >= 0;
    }
    assert FloorDiv(x, k) == x / k;
    assert FloorDiv(y, k) == y / k;
    // integer division by positive divisor is monotone on non-negative operands
    assert x / k <= y / k;
  } else if y < 0 {
    // both negative: FloorDiv uses (a - k + 1) / k which is monotone in a
    assert FloorDiv(x, k) == (x - k + 1) / k;
    assert FloorDiv(y, k) == (y - k + 1) / k;
    calc {
      x - k + 1;
      <= y - k + 1;
    }
    assert (x - k + 1) / k <= (y - k + 1) / k;
  } else {
    // x < 0 <= y
    assert FloorDiv(x, k) == (x - k + 1) / k;
    assert FloorDiv(y, k) == y / k;
    calc {
      x - k + 1;
      <= x;
      <= y;
    }
    assert (x - k + 1) / k <= y / k;
  }
}

lemma CountDivisibles_nonneg(k: int, a: int, b: int)
  requires ValidInput(k, a, b)
  ensures CountDivisiblesInRange(k, a, b) >= 0
{
  // monotonicity of FloorDiv gives FloorDiv(a-1,k) <= FloorDiv(b,k)
  FloorDiv_monotone(k, a - 1, b);
  assert FloorDiv(a - 1, k) <= FloorDiv(b, k);
  assert CountDivisiblesInRange(k, a, b) == FloorDiv(b, k) - FloorDiv(a - 1, k);
  assert FloorDiv(b, k) - FloorDiv(a - 1, k) >= 0;
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
  result := CountDivisiblesInRange(k, a, b);
  // Prove the postconditions: non-negativity follows from the helper lemma.
  CountDivisibles_nonneg(k, a, b);
}
// </vc-code>

