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
  if x <= y {
    // We want to prove that FloorDiv(x, d) <= FloorDiv(y, d).
    // This is equivalent to proving that for any n, FloorDiv(n, d) <= FloorDiv(n+1, d).
    // Let's use properties of integer division.
    // FloorDiv(n, d) is defined as floor(n/d).
    // The floor function is monotonic, i.e., if x <= y, then floor(x) <= floor(y).
    // Since x <= y and d > 0, we have x/d <= y/d.
    // Applying the floor function to both sides, floor(x/d) <= floor(y/d).
    // Which means FloorDiv(x, d) <= FloorDiv(y, d).

    // Explicit proof for Dafny's integer division behaviors based on signs:
    // Case 1: x >= 0 and y >= 0
    if x >= 0 && y >= 0 {
      calc {
        FloorDiv(x, d);
        x / d;
      }
      calc {
        FloorDiv(y, d);
        y / d;
      }
      // Integer division (a / b for positive b) is monotonic for non-negative a.
      // So, x <= y implies x / d <= y / d.
    }
    // Case 2: x < 0 and y < 0
    else if x < 0 && y < 0 {
      calc {
        FloorDiv(x, d);
        (x - d + 1) / d;
      }
      calc {
        FloorDiv(y, d);
        (y - d + 1) / d;
      }
      // If x <= y, then x - d + 1 <= y - d + 1.
      // For negative dividends, (a - d + 1) / d implements floor division.
      // The expression (val - d + 1) / d is monotonic for integer val.
      // So, if (x - d + 1) <= (y - d + 1), then (x - d + 1) / d <= (y - d + 1) / d.
    }
    // Case 3: x < 0 and y >= 0
    else if x < 0 && y >= 0 {
      // FloorDiv(x, d) will be non-positive, as x is negative.
      // If x % d == 0, then (x-d+1)/d is effectively x/d-1. but actually x/d.
      // (x - d + 1) / d for x < 0 with d > 0 results in a non-positive integer.
      // For instance, FloorDiv(-5, 3) = (-5 - 3 + 1)/3 = -7/3 = -3.
      // FloorDiv(0, 3) = 0/3 = 0.
      // So, FloorDiv(x, d) <= 0.

      // FloorDiv(y, d) will be non-negative, as y is non-negative.
      // So, FloorDiv(y, d) >= 0.

      // Therefore, FloorDiv(x, d) <= 0 <= FloorDiv(y, d), which means FloorDiv(x, d) <= FloorDiv(y, d).
    }
  }
}

lemma lemma_CountDivisiblesInRange_nonNegative(k: int, a: int, b: int)
  requires k > 0
  requires a <= b
  ensures CountDivisiblesInRange(k, a, b) >= 0
{
  // To prove CountDivisiblesInRange(k, a, b) >= 0, we need to show
  // FloorDiv(b, k) - FloorDiv(a - 1, k) >= 0, which is equivalent to
  // FloorDiv(b, k) >= FloorDiv(a - 1, k).
  //
  // We know that a <= b.
  // This implies a - 1 <= b.
  //
  // Now, we can use the monotonicity lemma for FloorDiv.
  // By lemma_FloorDiv_monotonic(a - 1, b, k), since (a - 1) <= b and k > 0,
  // we can conclude that FloorDiv(a - 1, k) <= FloorDiv(b, k).
  lemma_FloorDiv_monotonic(a - 1, b, k);
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

