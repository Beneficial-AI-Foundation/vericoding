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
lemma GcdDivides(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  decreases b
{
  var g := gcd(a, b);
  if b == 0 {
    assert g == a;
    assert a % a == 0;
  } else {
    assert g == gcd(b, a % b);
    GcdDivides(b, a % b);
    assert b % g == 0;
    assert (a % b) % g == 0;
    // Key insight: a = (a/b) * b + (a % b)
    // Since both b and (a % b) are divisible by g, so is a
    assert a % g == ((a/b) * b + (a % b)) % g == 0;
  }
}

lemma GcdPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
{
  // Follows directly from the ensures clause of gcd function
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
  
  // Since x > 0 and y > 0, we know g > 0
  GcdPositive(x, y);
  assert g > 0;
  
  // Compute reduced ratio
  GcdDivides(x, y);
  var x_reduced := x / g;
  var y_reduced := y / g;
  
  // Both x_reduced and y_reduced are positive since x, y, and g are positive
  assert x_reduced > 0 && y_reduced > 0;
  
  // Compute how many times the ratio fits
  var fits_horizontally := a / x_reduced;
  var fits_vertically := b / y_reduced;
  
  // Return the minimum
  if fits_horizontally <= fits_vertically {
    result := fits_horizontally;
  } else {
    result := fits_vertically;
  }
  
  // The result matches the expected function
  assert result == min(fits_horizontally, fits_vertically);
  assert result == ExpectedResult(a, b, x, y);
}
// </vc-code>

