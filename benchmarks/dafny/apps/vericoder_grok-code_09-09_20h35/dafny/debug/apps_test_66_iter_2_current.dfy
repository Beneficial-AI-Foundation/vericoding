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
  requires a > 0 && b >= 0
  decreases a + b
{
  if b == 0 then a else gcd(b, a % b)
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
  var base_num := t;
  var base_den := w * b;
  var g := gcd(base_num, base_den);
  var reduced_num := base_num / g;
  var reduced_den := base_den / g;
  var min_value: int := if reduced_num <= reduced_den then reduced_num else reduced_den;
  var max_value: int := if reduced_num <= reduced_den then reduced_den else reduced_num;
  numerator := min_value;
  denominator := max_value;
}
// </vc-code>

