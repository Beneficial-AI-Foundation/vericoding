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

lemma TotalBurningHoursStep(a: int, b: int)
  requires a >= b >= 2
  ensures TotalBurningHours(a, b) == a + TotalBurningHours(a / b, b)
{
  TotalBurningHoursUnfolding(a, b);
}

lemma TotalBurningHoursBase(a: int, b: int)
  requires 0 <= a < b && b >= 2
  ensures TotalBurningHours(a, b) == a
{
  TotalBurningHoursUnfolding(a, b);
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
    var old_current := current;
    total := total + current;
    current := current / b;
    
    // Help the verifier with the invariant
    assert old_current >= b;
    TotalBurningHoursStep(old_current, b);
    assert TotalBurningHours(old_current, b) == old_current + TotalBurningHours(old_current / b, b);
    assert TotalBurningHours(old_current, b) == old_current + TotalBurningHours(current, b);
    assert total == (total - old_current) + old_current;
    assert total + TotalBurningHours(current, b) == (total - old_current) + old_current + TotalBurningHours(current, b);
    assert total + TotalBurningHours(current, b) == (total - old_current) + TotalBurningHours(old_current, b);
  }
  
  // After the loop: current < b
  assert current < b;
  assert current >= 0;
  TotalBurningHoursBase(current, b);
  assert TotalBurningHours(current, b) == current;
  
  total := total + current;
  result := total;
  
  assert result == total;
  assert result == (total - current) + current;
  assert result == (total - current) + TotalBurningHours(current, b);
  assert result == TotalBurningHours(a, b);
}
// </vc-code>

