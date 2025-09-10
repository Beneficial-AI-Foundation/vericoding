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
lemma TotalBurningHoursLemma(a: int, b: int)
  requires a >= 0 && b >= 2
  ensures TotalBurningHours(a, b) == a + (if a >= b then TotalBurningHours(a / b, b) else 0)
  decreases a
{
  // This lemma explicitly states the relationship used in the loop invariant
}

lemma TotalBurningHoursNonNegative(a: int, b: int)
  requires a >= 0 && b >= 2
  ensures TotalBurningHours(a, b) >= 0
  decreases a
{
  if a == 0 {
  } else if a < b {
  } else {
    TotalBurningHoursNonNegative(a / b, b);
  }
}

lemma TotalBurningHoursPreservesInvariant(a: int, b: int)
  requires a >= 0 && b >= 2
  ensures TotalBurningHours(a, b) >= a
  decreases a
{
  if a == 0 {
  } else if a < b {
  } else {
    TotalBurningHoursPreservesInvariant(a / b, b);
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
  
  // Handle the case when current becomes 0
  if a == 0 {
    assert result == 0 && TotalBurningHours(a, b) == 0;
  }
}
// </vc-code>

