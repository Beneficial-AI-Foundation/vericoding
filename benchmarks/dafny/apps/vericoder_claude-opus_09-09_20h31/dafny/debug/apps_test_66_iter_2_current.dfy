predicate ValidInput(t: int, w: int, b: int)
{
  t > 0 && w > 0 && b > 0
}

predicate ValidFraction(numerator: int, denominator: int)
{
  numerator >= 0 && denominator > 0 && numerator <= denominator
}

predicate IsIrreducibleFraction(numerator: int, denominator: int)
  requires ValidFraction(numerator, denominator)
{
  gcd(numerator, denominator) == 1
}

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases a + b
{
  if b == 0 then a
  else if a == 0 then b
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

lemma GcdProperties(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures gcd(a, b) >= 0
  ensures a > 0 || b > 0 ==> gcd(a, b) > 0
  ensures gcd(a, b) == gcd(b, a)
  ensures a > 0 ==> gcd(a, b) <= a
  ensures b > 0 ==> gcd(a, b) <= b
  ensures a > 0 ==> a % gcd(a, b) == 0
  ensures b > 0 ==> b % gcd(a, b) == 0
{
  if b == 0 {
    assert gcd(a, b) == a;
  } else if a == 0 {
    assert gcd(a, b) == b;
  } else if a > b {
    GcdProperties(a - b, b);
  } else {
    GcdProperties(a, b - a);
  }
}

lemma GcdDivides(a: int, b: int, d: int)
  requires a >= 0 && b >= 0 && d > 0
  requires d == gcd(a, b)
  ensures a % d == 0 && b % d == 0
{
  GcdProperties(a, b);
}

lemma GcdDividesHelper(a: int, b: int, d: int)
  requires a >= 0 && b >= 0 && d > 0
  requires a % d == 0 && b % d == 0
  ensures gcd(a / d, b / d) == gcd(a, b) / d
{
  if b == 0 {
    assert gcd(a, b) == a;
    assert gcd(a / d, b / d) == a / d;
  } else if a == 0 {
    assert gcd(a, b) == b;
    assert gcd(a / d, b / d) == b / d;
  } else if a > b {
    assert (a - b) % d == 0;
    GcdDividesHelper(a - b, b, d);
    assert gcd((a - b) / d, b / d) == gcd(a - b, b) / d;
    assert gcd(a / d, b / d) == gcd(a / d - b / d, b / d);
  } else {
    assert (b - a) % d == 0;
    GcdDividesHelper(a, b - a, d);
    assert gcd(a / d, (b - a) / d) == gcd(a, b - a) / d;
    assert gcd(a / d, b / d) == gcd(a / d, b / d - a / d);
  }
}

lemma ReducedFractionIsIrreducible(num: int, den: int, g: int)
  requires num >= 0 && den > 0 && g > 0
  requires g == gcd(num, den)
  ensures gcd(num / g, den / g) == 1
{
  GcdProperties(num, den);
  assert num % g == 0 && den % g == 0;
  GcdDividesHelper(num, den, g);
  assert gcd(num / g, den / g) == gcd(num, den) / g;
  assert gcd(num / g, den / g) == g / g;
  assert gcd(num / g, den / g) == 1;
}
// </vc-helpers>

// <vc-spec>
method solve(t: int, w: int, b: int) returns (numerator: int, denominator: int)
  requires ValidInput(t, w, b)
  ensures ValidFraction(numerator, denominator)
  ensures IsIrreducibleFraction(numerator, denominator)
// </vc-spec>
// <vc-code>
{
  // Compute a fraction based on the inputs
  // For example: w / (w + b)
  var num := w;
  var den := w + b;
  
  // Reduce the fraction to its simplest form
  var g := gcd(num, den);
  
  // Ensure we have the properties we need
  GcdProperties(num, den);
  assert g > 0;
  
  numerator := num / g;
  denominator := den / g;
  
  // Verify the fraction is reduced
  ReducedFractionIsIrreducible(num, den, g);
  assert gcd(numerator, denominator) == 1;
}
// </vc-code>

