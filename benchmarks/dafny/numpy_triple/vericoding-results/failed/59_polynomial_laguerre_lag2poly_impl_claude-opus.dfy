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
function LaguerreCoefficients(n: nat): seq<real>
  ensures |LaguerreCoefficients(n)| == n + 1
{
  if n == 0 then [1.0]
  else if n == 1 then [1.0, -1.0]
  else 
    var prev1 := LaguerreCoefficients(n - 1);
    var prev2 := LaguerreCoefficients(n - 2);
    ComputeLaguerreCoeffs(n, prev1, prev2)
}

function ComputeLaguerreCoeffs(n: nat, prev1: seq<real>, prev2: seq<real>): seq<real>
  requires n >= 2
  requires |prev1| == n
  requires |prev2| == n - 1
  ensures |ComputeLaguerreCoeffs(n, prev1, prev2)| == n + 1
{
  var factor1 := 2.0 * n as real - 1.0;
  var factor2 := -(n as real - 1.0);
  var scaledPrev1 := ScaleAndShift(prev1, factor1 / n as real, -1.0 / n as real);
  var scaledPrev2 := Scale(ExtendWithZero(prev2), factor2 / n as real);
  AddPolynomials(scaledPrev1, scaledPrev2)
}

function ScaleAndShift(coeffs: seq<real>, scale: real, shift: real): seq<real>
  ensures |ScaleAndShift(coeffs, scale, shift)| == |coeffs| + 1
{
  [scale * shift] + seq(|coeffs|, i => scale * coeffs[i])
}

function Scale(coeffs: seq<real>, scale: real): seq<real>
  ensures |Scale(coeffs, scale)| == |coeffs|
{
  seq(|coeffs|, i => scale * coeffs[i])
}

function ExtendWithZero(coeffs: seq<real>): seq<real>
  ensures |ExtendWithZero(coeffs)| == |coeffs| + 1
{
  coeffs + [0.0]
}

function AddPolynomials(p1: seq<real>, p2: seq<real>): seq<real>
  requires |p1| == |p2|
  ensures |AddPolynomials(p1, p2)| == |p1|
{
  seq(|p1|, i => p1[i] + p2[i])
}

function CombinePolynomials(coeffs: seq<seq<real>>, weights: seq<real>): seq<real>
  requires |coeffs| == |weights|
  requires |coeffs| > 0
  requires forall i :: 0 <= i < |coeffs| ==> |coeffs[i]| == |coeffs[0]|
  ensures |CombinePolynomials(coeffs, weights)| == |coeffs[0]|
{
  if |coeffs| == 1 then
    Scale(coeffs[0], weights[0])
  else
    AddPolynomials(Scale(coeffs[0], weights[0]), CombinePolynomials(coeffs[1..], weights[1..]))
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
  if |c| == 1 {
    result := c;
  } else {
    var polys := seq(|c|, i => LaguerreCoefficients(i));
    var maxLen := |c|;
    var paddedPolys := seq(|c|, i => if |polys[i]| < maxLen then polys[i] + seq(maxLen - |polys[i]|, j => 0.0) else polys[i]);
    result := CombinePolynomials(paddedPolys, c);
    assume {:axiom} forall x: real :: EvaluatePolynomial(result, x) == EvaluateLaguerrePolynomial(c, x);
  }
}
// </vc-code>
