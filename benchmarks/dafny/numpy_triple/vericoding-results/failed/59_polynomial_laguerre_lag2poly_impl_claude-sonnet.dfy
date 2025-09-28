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
/* helper modified by LLM (iteration 5): Implementing coefficient transformation matrix approach */
function LaguerreToPolyMatrix(n: nat, i: nat, j: nat): real
  requires i < n && j < n
{
  if i == 0 && j == 0 then 1.0
  else if i == 1 && j == 0 then 1.0
  else if i == 1 && j == 1 then -1.0
  else if i > 1 then
    var coeff1 := (2.0 * i as real - 1.0) / i as real;
    var coeff2 := -1.0 / i as real;
    var coeff3 := -(i as real - 1.0) / i as real;
    if j == 0 then coeff1 * LaguerreToPolyMatrix(n, i-1, j) + coeff3 * LaguerreToPolyMatrix(n, i-2, j)
    else if j == 1 then coeff2 * LaguerreToPolyMatrix(n, i-1, j-1) + coeff1 * LaguerreToPolyMatrix(n, i-1, j) + coeff3 * LaguerreToPolyMatrix(n, i-2, j)
    else coeff2 * LaguerreToPolyMatrix(n, i-1, j-1) + coeff1 * LaguerreToPolyMatrix(n, i-1, j) + coeff3 * LaguerreToPolyMatrix(n, i-2, j)
  else 0.0
}

function ComputePolyCoeff(c: seq<real>, degree: nat): real
  requires |c| > 0
  requires degree < |c|
{
  var sum := 0.0;
  var i := 0;
  while i < |c|
    invariant 0 <= i <= |c|
  {
    sum := sum + c[i] * LaguerreToPolyMatrix(|c|, i, degree);
    i := i + 1;
  }
  sum
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
{
  /* code modified by LLM (iteration 5): Using matrix transformation approach */
  if |c| == 1 {
    result := c;
  } else {
    result := seq(|c|, j requires 0 <= j < |c| => ComputePolyCoeff(c, j));
  }
}
// </vc-code>
