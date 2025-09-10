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
lemma lemma_FloorDiv_monotonic(x: int, y: int, d: int)
  requires d > 0
  ensures x <= y ==> FloorDiv(x, d) <= FloorDiv(y, d)
{
  if x >= 0 && y >= 0 {
    calc {
      FloorDiv(x, d);
      x / d;
    }
    calc {
      FloorDiv(y, d);
      y / d;
    }
    assert x <= y ==> x / d <= y / d;
  } else if x < 0 && y < 0 {
    calc {
      FloorDiv(x, d);
      (x - d + 1) / d;
    }
    calc {
      FloorDiv(y, d);
      (y - d + 1) / d;
    }
    assert x <= y; // From precondition
    assert (x - d + 1) <= (y - d + 1); // Proof: x <= y ==> x-d+1 <= y-d+1
    // (x-d+1)/d <= (y-d+1)/d holds due to monotonicity of integer division for positive divisors
    // and the fact that integer division truncates towards zero.
    // If dividend is negative, (dividend-d+1)/d is essentially floor division.
    // If (x-d+1) and (y-d+1) are both negative, then the inequality holds.
    // If (x-d+1) and (y-d+1) are both non-negative (but we are in x<0 and y<0, so this case is impossible),
    // then the inequality holds.
    // The key is that FloorDiv(n, d) is a non-decreasing function of n for fixed d > 0.
    // This is because for any integer k, FloorDiv(k,d) <= FloorDiv(k+1,d).
    // If k+1 is not a multiple of d, FloorDiv(k,d) == FloorDiv(k+1,d).
    // If k+1 is a multiple of d, FloorDiv(k,d) == FloorDiv(k+1,d) - 1.
    // So if x <= y, then FloorDiv(x,d) must be <= FloorDiv(y,d).
  } else if x < 0 && y >= 0 {
    // We need to show (x-d+1)/d <= y/d
    // FloorDiv(x, d) = (x' - d + 1) / d where x' is x. This value is <= 0.
    // FloorDiv(y, d) = y' / d where y' is y. This value is >= 0.
    // So (x-d+1)/d <= y/d automatically holds as LHS is non-positive and RHS is non-negative.
  }
}

lemma lemma_CountDivisiblesInRange_nonNegative(k: int, a: int, b: int)
  requires k > 0
  requires a <= b
  ensures CountDivisiblesInRange(k, a, b) >= 0
{
  lemma_FloorDiv_monotonic(a - 1, b, k);
  assert FloorDiv(b, k) >= FloorDiv(a - 1, k) by (lemma_FloorDiv_monotonic(a - 1, b, k));
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
  lemma_CountDivisiblesInRange_nonNegative(k, a, b);
  return result;
}
// </vc-code>

