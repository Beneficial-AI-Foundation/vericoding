predicate ValidInput(a: int, b: int)
{
  a >= 1 && a <= 1000 && b >= 2 && b <= 1000
}

function TotalBurningHours(a: int, b: int): int
  requires a >= 0 && b >= 2
  ensures TotalBurningHours(a, b) >= a
  decreases a
{
  if a == 0 then 0
  else if a < b then a
  else a + TotalBurningHours(a / b, b)
}

// <vc-helpers>
lemma TotalBurningHoursLemma(a: int, b: int, divisor: int)
  requires a >= 0 && b >= 2
  requires divisor >= 2
  ensures TotalBurningHours(a, b) == a + TotalBurningHours(a / b, b)
  decreases a
{
  if a < b {
    // Base case: a < b, so TotalBurningHours(a, b) = a
    // The equation becomes: a == a + TotalBurningHours(a / b, b)
    // But since a < b, a / b = 0, and TotalBurningHours(0, b) = 0
    // So it's: a == a + 0, which holds
  } else {
    // Recursive case: a >= b
    // The function definition already gives us TotalBurningHours(a, b) = a + TotalBurningHours(a / b, b)
    // So the equation holds by definition
  }
}

lemma TotalBurningHoursNonNegative(a: int, b: int)
  requires a >= 0 && b >= 2
  ensures TotalBurningHours(a, b) >= 0
  decreases a
{
  // Proof that TotalBurningHours is always non-negative
  if a == 0 {
    // Base case: TotalBurningHours(0, b) = 0 >= 0
  } else if a < b {
    // Case: TotalBurningHours(a, b) = a >= 0 (since a >= 0)
  } else {
    // Recursive case: TotalBurningHours(a, b) = a + TotalBurningHours(a / b, b) >= 0 + 0 = 0
    TotalBurningHoursNonNegative(a / b, b);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
  requires ValidInput(a, b)
  ensures result >= a
  ensures result == TotalBurningHours(a, b)
// </vc-spec>
// <vc-code>
{
  var current := a;
  result := 0;
  
  while current > 0
    invariant result >= 0
    invariant result + current >= a
    invariant result + TotalBurningHours(current, b) == TotalBurningHours(a, b)
    decreases current
  {
    if current < b {
      result := result + current;
      current := 0;
    } else {
      result := result + current;
      current := current / b;
    }
  }
}
// </vc-code>

