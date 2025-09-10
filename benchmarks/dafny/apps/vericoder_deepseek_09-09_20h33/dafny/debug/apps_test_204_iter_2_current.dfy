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
lemma LemmaGCDMultiple(a: int, b: int, x: int, g: int)
  requires a >= 0 && b >= 0 && x > 0 && g > 0
  requires g == gcd(a, b)
  ensures a % g == 0 && b % g == 0
  ensures (a / g) * g == a
  ensures (b / g) * g == b
{
  if b == 0 {
  } else {
    LemmaGCDMultiple(b, a % b, x, g);
  }
}

lemma LemmaGCDDivisor(a: int, b: int, d: int)
  requires a >= 0 && b >= 0 && d > 0
  requires d == gcd(a, b)
  ensures gcd(a / d, b / d) == 1
{
  if b == 0 {
  } else {
    var g := gcd(b, a % b);
    LemmaGCDDivisor(b, a % b, g);
  }
}

lemma LemmaMinProperties(a: int, b: int, c: int)
  requires a >= 0 && b >= 0 && c >= 0
  ensures min(a, b) <= a && min(a, b) <= b
  ensures min(a, b) == a || min(a, b) == b
  ensures c <= a && c <= b ==> c <= min(a, b)
{
}

lemma LemmaDivisionProperties(x: int, g: int)
  requires x > 0 && g > 0
  requires x % g == 0
  ensures (x / g) * g == x
{
}

lemma LemmaGCDZero(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures gcd(a, b) == 0 ==> a == 0 && b == 0
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
    if x > 0 {} else { assert false; }
    if y > 0 {} else { assert false; }
  };
  
  LemmaGCDMultiple(x, y, x, g);
  assert x % g == 0 && y % g == 0;
  LemmaDivisionProperties(x, g);
  LemmaDivisionProperties(y, g);
  
  var x_reduced := x / g;
  var y_reduced := y / g;
  
  var max_possible_x := a / x_reduced;
  var max_possible_y := b / y_reduced;
  
  result := min(max_possible_x, max_possible_y);
}
// </vc-code>

