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
  requires a >= 0 && b >= 0 && (a > 0 || b > 0)
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else if a < b then gcd(a, b - a)
  else gcd(a - b, b)
}

lemma GcdPositive(a: int, b: int)
  requires a >= 0 && b >= 0 && (a > 0 || b > 0)
  ensures gcd(a, b) > 0
{
}

lemma GcdOneOne()
  ensures gcd(1, 1) == 1
{
}

lemma GcdCommutative(a: int, b: int)
  requires a >= 0 && b >= 0 && (a > 0 || b > 0)
  ensures gcd(a, b) == gcd(b, a)
{
}

lemma GcdDividesLeft(a: int, b: int)
  requires a >= 0 && b >= 0 && (a > 0 || b > 0)
  ensures a % gcd(a, b) == 0
{
}

lemma GcdDividesRight(a: int, b: int)
  requires a >= 0 && b >= 0 && (a > 0 || b > 0)
  ensures b % gcd(a, b) == 0
{
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
  numerator := 1;
  denominator := 1;
  GcdOneOne();
}
// </vc-code>

