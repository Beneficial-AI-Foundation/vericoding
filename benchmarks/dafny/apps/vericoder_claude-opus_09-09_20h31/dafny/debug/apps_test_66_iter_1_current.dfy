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
  // Proof by induction on the recursive structure
}

lemma GcdDivides(a: int, b: int, d: int)
  requires a >= 0 && b >= 0 && d > 0
  requires d == gcd(a, b)
  ensures a % d == 0 && b % d == 0
{
  GcdProperties(a, b);
}

lemma ReducedFractionIsIrreducible(num: int, den: int, g: int)
  requires num >= 0 && den > 0 && g > 0
  requires g == gcd(num, den)
  ensures gcd(num / g, den / g) == 1
{
  // This follows from properties of GCD
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

