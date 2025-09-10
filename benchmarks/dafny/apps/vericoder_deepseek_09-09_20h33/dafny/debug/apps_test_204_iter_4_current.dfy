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
lemma LemmaGCDPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
{
}

lemma LemmaGCDMultiple(a: int, b: int, x: int, g: int)
  requires a > 0 && b > 0 && g == gcd(a, b)
  ensures x % g == 0 when x == a || x == b
{
}

lemma LemmaDivisionProperties(n: int, d: int)
  requires d > 0
  ensures n / d >= 0
{
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
  assert g > 0 by {
    LemmaGCDPositive(x, y);
  };
  
  assert x % g == 0;
  assert y % g == 0;
  
  var x_reduced := x / g;
  var y_reduced := y / g;
  
  var max_possible_x := a / x_reduced;
  var max_possible_y := b / y_reduced;
  
  result := min(max_possible_x, max_possible_y);
}
// </vc-code>

