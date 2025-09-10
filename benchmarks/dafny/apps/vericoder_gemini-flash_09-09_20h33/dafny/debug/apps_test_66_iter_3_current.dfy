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
  decreases a, b
{
  if a == 0 then b
  else if b == 0 then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
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
  var commonDivisor := gcd(t * w, t * w + b);
  numerator := (t * w) / commonDivisor;
  denominator := (t * w + b) / commonDivisor;

  assert ValidFraction(numerator, denominator) by {
    assert commonDivisor > 0; // Follows from gcd properties and positive inputs
    assert t * w >= 0; // From ValidInput
    assert t * w + b > 0; // From ValidInput
    assert numerator >= 0;
    assert denominator > 0;
    calc {
      (t * w) / commonDivisor * commonDivisor;
      t * w;
    }
    calc {
      (t * w + b) / commonDivisor * commonDivisor;
      t * w + b;
    }
    assert (t * w) <= (t * w + b);
    assert (t * w) / commonDivisor <= (t * w + b) / commonDivisor;
  };
  assert IsIrreducibleFraction(numerator, denominator) by {
    assert gcd(numerator, denominator) == gcd((t * w) / commonDivisor, (t * w + b) / commonDivisor);
    // Property of gcd: gcd(a/g, b/g) == 1 if g == gcd(a,b)
    assert gcd(t * w, t * w + b) == commonDivisor;
    assert gcd((t * w) / commonDivisor, (t * w + b) / commonDivisor) == 1;
  };
}
// </vc-code>

