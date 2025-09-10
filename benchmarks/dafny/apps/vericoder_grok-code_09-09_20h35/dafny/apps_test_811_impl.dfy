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
ghost method CalcTotal(a: int, b: int) returns (r: int)
  requires a >= 0 && b >= 2
  ensures r == TotalBurningHours(a, b)
{
  r := 0;
  var c := a;
  while c > 0
    decreases c
  {
    r := r + c;
    c := c / b;
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
  result := 0;
  var current: int := a;
  while current > 0
    invariant 0 <= current <= a
    invariant result + TotalBurningHours(current, b) == TotalBurningHours(a, b)
    decreases current
  {
    if current < b {
      result := result + current;
      current := 0;
      assert TotalBurningHours(old(current), b) == old(current);
    } else {
      result := result + current;
      current := current / b;
      assert TotalBurningHours(old(current), b) == old(current) + TotalBurningHours(current, b);
    }
  }
}
// </vc-code>

