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
  var n := a;
  
  while n >= b
    invariant n >= 0
    invariant total + TotalBurningHours(n, b) == TotalBurningHours(a, b)
    decreases n
  {
    total := total + n;
    n := n / b;
  }
  
  total := total + n;
  return total;
}
// </vc-code>

