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
lemma TotalBurningHoursUnfolding(a: int, b: int)
  requires a >= 0 && b >= 2
  ensures TotalBurningHours(a, b) == if a == 0 then 0 else if a < b then a else a + TotalBurningHours(a / b, b)
{
  // This follows directly from the function definition
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
  var total := 0;
  var current := a;
  
  while current >= b
    invariant 0 <= current <= a
    invariant b >= 2
    invariant total + TotalBurningHours(current, b) == TotalBurningHours(a, b)
    decreases current
  {
    total := total + current;
    current := current / b;
  }
  
  total := total + current;
  result := total;
  
  // Prove the postcondition
  assert current < b;
  assert current >= 0;
  TotalBurningHoursUnfolding(current, b);
  assert TotalBurningHours(current, b) == current;
  assert result == total == total - current + current == (total - current) + TotalBurningHours(current, b);
}
// </vc-code>

