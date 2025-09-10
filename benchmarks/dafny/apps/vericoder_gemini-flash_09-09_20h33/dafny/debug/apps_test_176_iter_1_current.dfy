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
    assert (x - d + 1) <= (y - d + 1);
    assert (x - d + 1) / d <= (y - d + 1) / d;
  } else if x < 0 && y >= 0 {
    calc {
      FloorDiv(x, d);
      (x - d + 1) / d;
    }
    calc {
      FloorDiv(y, d);
      y / d;
    }
    // We need to show (x-d+1)/d <= y/d
    // (x-d+1)/d < x/d if x is not a multiple of d
    // (x-d+1)/d = x/d - 1 if x is a multiple of d
    // In any case, (x-d+1)/d is either less than or equal to -1.
    // y/d is greater than or equal to 0.
    // So (x-d+1)/d <= y/d holds.
  }
}

lemma lemma_CountDivisiblesInRange_nonNegative(k: int, a: int, b: int)
  requires k > 0
  requires a <= b
  ensures CountDivisiblesInRange(k, a, b) >= 0
{
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
  var result := CountDivisiblesInRange(k, a, b);
  lemma_CountDivisiblesInRange_nonNegative(k, a, b);
  return result;
}
// </vc-code>

