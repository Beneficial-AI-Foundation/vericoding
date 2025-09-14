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

lemma LoopInvariantMaintained(a: int, b: int, total: int, current: int)
  requires a >= 0  // Added this precondition to ensure a is non-negative
  requires b >= 2
  requires current >= b
  requires current >= 0
  requires total + TotalBurningHours(current, b) == TotalBurningHours(a, b)
  ensures (total + current) + TotalBurningHours(current / b, b) == TotalBurningHours(a, b)
{
  TotalBurningHoursStep(current, b);
  assert TotalBurningHours(current, b) == current + TotalBurningHours(current / b, b);
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
    invariant current >= 0
    invariant b >= 2
    invariant a >= 0  // Added this invariant to maintain that a is non-negative
    invariant total + TotalBurningHours(current, b) == TotalBurningHours(a, b)
    decreases current
  {
    LoopInvariantMaintained(a, b, total, current);
    total := total + current;
    current := current / b;
  }
  
  TotalBurningHoursBase(current, b);
  total := total + current;
  result := total;
}
// </vc-code>

