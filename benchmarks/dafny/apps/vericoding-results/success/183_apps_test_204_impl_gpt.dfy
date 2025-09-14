predicate ValidInput(a: int, b: int, x: int, y: int)
{
  a > 0 && b > 0 && x > 0 && y > 0
}

function gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures gcd(a, b) >= 0
  ensures a > 0 ==> gcd(a, b) > 0
  ensures b > 0 ==> gcd(a, b) > 0
  ensures gcd(a, b) <= a || a == 0
  ensures gcd(a, b) <= b || b == 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

function min(a: int, b: int): int
{
  if a <= b then a else b
}

function ExpectedResult(a: int, b: int, x: int, y: int): int
  requires ValidInput(a, b, x, y)
{
  var g := gcd(x, y);
  var x_reduced := x / g;
  var y_reduced := y / g;
  min(a / x_reduced, b / y_reduced)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, x: int, y: int) returns (result: int)
  requires ValidInput(a, b, x, y)
  ensures result >= 0
  ensures result == ExpectedResult(a, b, x, y)
// </vc-spec>
// <vc-code>
{
  var g := gcd(x, y);
  assert g > 0;

  // From gcd's postconditions and x > 0, y > 0
  assert g <= x || x == 0;
  assert x != 0;
  assert g <= x;
  assert g <= y || y == 0;
  assert y != 0;
  assert g <= y;

  var xr := x / g;
  var yr := y / g;

  // Show reduced denominators are positive (hence non-zero)
  assert xr >= 1;
  assert yr >= 1;

  result := min(a / xr, b / yr);

  // Postconditions
  assert result >= 0;
  assert result == ExpectedResult(a, b, x, y);
}
// </vc-code>

