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
function max(a: int, b: int): int
{
  if a >= b then a else b
}

function gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases max(a, b)
{
  if b == 0 then a
  else if a == 0 then b
  else gcd(b, a % b)
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
  assert base_num % g == 0;
  assert base_den % g == 0;
  var reduced_num := base_num / g;
  var reduced_den := base_den / g;
  if reduced_num <= reduced_den {
    numerator := reduced_num;
    denominator := reduced_den;
  } else {
    numerator := reduced_den;
    denominator := reduced_num;
  }
}
// </vc-code>

