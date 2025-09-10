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
lemma GcdProperties(x: int, y: int)
  requires x > 0 && y > 0
  ensures gcd(x, y) > 0
  ensures (x / gcd(x, y)) > 0
  ensures (y / gcd(x, y)) > 0
  ensures x % gcd(x, y) == 0
  ensures y % gcd(x, y) == 0
{
  var g := gcd(x, y);
  
  if y == 0 {
    assert g == x;
  } else {
    GcdDivisibility(x, y);
  }
}

lemma GcdDivisibility(x: int, y: int)
  requires x > 0 && y > 0
  ensures x % gcd(x, y) == 0
  ensures y % gcd(x, y) == 0
  decreases y
{
  if y == 0 {
    assert gcd(x, y) == x;
  } else {
    assert x % y >= 0 && x % y < y;
    if x % y > 0 {
      GcdDivisibility(y, x % y);
    }
  }
}

lemma DivisionProperties(a: int, b: int, x: int, y: int)
  requires ValidInput(a, b, x, y)
  ensures var g := gcd(x, y);
          var x_reduced := x / g;
          var y_reduced := y / g;
          a / x_reduced >= 0 && b / y_reduced >= 0
{
  var g := gcd(x, y);
  GcdProperties(x, y);
}
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
  GcdProperties(x, y);
  var x_reduced := x / g;
  var y_reduced := y / g;
  DivisionProperties(a, b, x, y);
  var option1 := a / x_reduced;
  var option2 := b / y_reduced;
  result := min(option1, option2);
}
// </vc-code>

