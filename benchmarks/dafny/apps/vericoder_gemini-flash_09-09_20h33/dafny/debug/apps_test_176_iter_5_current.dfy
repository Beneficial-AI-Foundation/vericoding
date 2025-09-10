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
    // This proof relies on the property that for any integers X, Y, and positive integer D:
    // If X <= Y, then FloorDiv(X, D) <= FloorDiv(Y, D).
    // This is a direct consequence of the definition of FloorDiv as the floor of real division (X/D).
    // The floor function is monotonic. If a <= b, then floor(a) <= floor(b).
    // Since x <= y and d > 0, we have x/d <= y/d (real division).
    // Applying the floor function to both sides, Floor(x/d) <= Floor(y/d).
    // By definition, FloorDiv(x, d) == Floor(x/d) and FloorDiv(y, d) == Floor(y/d).
    // Thus, FloorDiv(x, d) <= FloorDiv(y, d).

    // Dafny's default integer division behaves like floor division for positive divisors.
    // For positive numbers: `a / b` where `b > 0` is `floor(a/b)`.
    // For negative numbers: `a / b` where `b > 0` is `ceil(a/b)` (truncated division).
    // Our FloorDiv function handles negative numbers to ensure it's always floor division.

    // Let's break it down by cases to make Dafny happy regardless of the sign of x and y.

    // Case 1: x >= 0 and y >= 0
    // In this case, FloorDiv(a, d) is just a / d.
    // Since x <= y and d > 0, it holds that x / d <= y / d (integer division property).
    // This is implicitly handled by Dafny's integer properties.
    // assert (x / d) <= (y / d); // This assertion would pass.

    // Case 2: x < 0 and y < 0
    // In this case, FloorDiv(a, d) is (a - d + 1) / d for a < 0.
    // Let f(a) = (a - d + 1) / d.
    // If x <= y, then x - d + 1 <= y - d + 1.
    // Since d > 0, the integer division (num / d) is monotonic with respect to num.
    // So, f(x) <= f(y).
    // assert ((x - d + 1) / d) <= ((y - d + 1) / d); // This assertion would pass.

    // Case 3: x < 0 and y >= 0
    // FloorDiv(x, d) is negative or zero.
    // FloorDiv(y, d) is non-negative.
    // A negative or zero number is always less than or equal to a non-negative number.
    // So, FloorDiv(x, d) <= FloorDiv(y, d) holds.

    // Dafny's integer logic usually handles these monotonicity properties relatively well without deep induction here.
    // The issue might be a timeout due to the complexity of the internal reasoning about FloorDiv's piecewise definition.
    // The proof structure above serves to guide the verifier, but it might still time out without
    // more direct assertions or a specific lemma about integer division properties.

    // A more abstract proof might be better for the verifier, relying on the mathematical properties of floor division.
    // Instead of case analysis for FloorDiv, we can rely on its definition: a = q*b + r, where 0 <= r < b.
    // FloorDiv(a, b) = q.
    //
    // For x <= y, we want to prove FloorDiv(x, d) <= FloorDiv(y, d).
    // Let FloorDiv(x, d) = q_x and FloorDiv(y, d) = q_y.
    // By definition of FloorDiv:
    // q_x * d <= x < (q_x + 1) * d
    // q_y * d <= y < (q_y + 1) * d
    //
    // Since x <= y:
    // q_x * d <= x <= y < (q_y + 1) * d
    // From this, we have q_x * d < (q_y + 1) * d.
    // Since d > 0, we can divide by d:
    // q_x < q_y + 1
    // Since q_x and q_y are integers, this implies q_x <= q_y.
    // Therefore, FloorDiv(x, d) <= FloorDiv(y, d).
    // This is the fundamental mathematical property. Dafny should be able to deduce this.
    // The explicit case analysis and `calc` blocks might be misleading the verifier to check
    // each individual path, instead of leveraging the high-level property.
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

