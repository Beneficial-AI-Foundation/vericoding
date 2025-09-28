// <vc-preamble>
// Helper function to evaluate a Laguerre polynomial at a given point
function EvaluateLaguerrePolynomial(coeffs: seq<real>, x: real): real
  requires |coeffs| > 0
{
  if |coeffs| == 1 then
    coeffs[0]
  else
    coeffs[0] + EvaluateLaguerrePolynomial(coeffs[1..], x) * LaguerrePolynomialValue(|coeffs| - 1, x)
}

// Helper function to compute the value of the nth Laguerre polynomial at x
function LaguerrePolynomialValue(n: nat, x: real): real
{
  if n == 0 then 1.0
  else if n == 1 then 1.0 - x
  else 
    ((2.0 * n as real - 1.0 - x) * LaguerrePolynomialValue(n - 1, x) - (n as real - 1.0) * LaguerrePolynomialValue(n - 2, x)) / n as real
}

// Helper function to evaluate a standard polynomial at a given point  
function EvaluatePolynomial(coeffs: seq<real>, x: real): real
  requires |coeffs| > 0
{
  if |coeffs| == 1 then
    coeffs[0]
  else
    coeffs[0] + x * EvaluatePolynomial(coeffs[1..], x)
}

// Convert a Laguerre series to a polynomial
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed recursive function with proper bounds checking */
function LaguerreToPolynomialHelper(i: nat, j: nat): real
  requires j <= i
{
  if i == 0 then 1.0
  else if j == i then -LaguerreToPolynomialHelper(i-1, i-1) / i as real
  else if j == 0 then (1.0 + (i-1) as real) * LaguerreToPolynomialHelper(i-1, 0) / i as real
  else ((j+1) as real * LaguerreToPolynomialHelper(i-1, j+1) + (2*j+1-i) as real * LaguerreToPolynomialHelper(i-1, j) - LaguerreToPolynomialHelper(i-1, j-1)) / i as real
}
// </vc-helpers>

// <vc-spec>
method Lag2Poly(c: seq<real>) returns (result: seq<real>)
  requires |c| > 0
  ensures |result| == |c|
  ensures forall x: real :: EvaluatePolynomial(result, x) == EvaluateLaguerrePolynomial(c, x)
  ensures |c| == 1 ==> result == c
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error with proper while loop syntax */
{
  result := [c[0]];
  var i: int := 1;
  while i < |c|
    invariant 0 <= i <= |c|
    invariant |result| == i
  {
    var newPoly: seq<real> := [];
    var j: int := 0;
    while j <= i
      invariant 0 <= j <= i+1
      invariant |newPoly| == j
    {
      var coeff: real := c[i] * LaguerreToPolynomialHelper(i, j);
      if j < i then {
        coeff := coeff + result[j];
      }
      newPoly := newPoly + [coeff];
      j := j + 1;
    }
    result := newPoly;
    i := i + 1;
  }
}
// </vc-code>
