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
lemma TotalBurningHoursCorrectness(a: int, b: int)
  requires a >= 0 && b >= 2
  ensures TotalBurningHours(a, b) >= a
{
  if a == 0 {
    assert TotalBurningHours(a, b) == 0 && a == 0;
  } else if a < b {
    assert TotalBurningHours(a, b) == a;
  } else {
    TotalBurningHoursCorrectness(a / b, b);
    assert TotalBurningHours(a, b) == a + TotalBurningHours(a / b, b);
    assert TotalBurningHours(a / b, b) >= a / b >= 0;
    assert TotalBurningHours(a, b) >= a;
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
  var current_a := a;
  var total := 0;
  
  while current_a > 0
    invariant current_a >= 0
    invariant total + TotalBurningHours(current_a, b) == TotalBurningHours(a, b)
    decreases current_a
  {
    if current_a < b {
      total := total + current_a;
      current_a := 0;
    } else {
      total := total + current_a;
      current_a := current_a / b;
    }
  }
  
  result := total;
}
// </vc-code>

