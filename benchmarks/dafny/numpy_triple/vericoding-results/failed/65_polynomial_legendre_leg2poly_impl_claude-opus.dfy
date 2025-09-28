// <vc-preamble>
// Function to compute Legendre polynomial L_n(x)
function LegendrePolynomial(n: nat, x: real): real
  decreases n
{
  if n == 0 then 1.0
  else if n == 1 then x
  else ((2.0 * (n-1) as real + 1.0) * x * LegendrePolynomial(n-1, x) - (n-1) as real * LegendrePolynomial(n-2, x)) / (n as real)
}

// Function to evaluate polynomial with monomial coefficients
function EvaluatePolynomial(coeffs: seq<real>, x: real): real
{
  if |coeffs| == 0 then 0.0
  else coeffs[0] + (if |coeffs| == 1 then 0.0 else x * EvaluatePolynomial(coeffs[1..], x))
}

// Function to evaluate Legendre series
function EvaluateLegendre(c: seq<real>, x: real): real
{
  if |c| == 0 then 0.0
  else c[0] * LegendrePolynomial(0, x) + EvaluateLegendreHelper(c[1..], x, 1)
}

// Helper function for EvaluateLegendre with index tracking
function EvaluateLegendreHelper(c: seq<real>, x: real, startIndex: nat): real
{
  if |c| == 0 then 0.0
  else c[0] * LegendrePolynomial(startIndex, x) + EvaluateLegendreHelper(c[1..], x, startIndex + 1)
}

// Method to convert Legendre series coefficients to polynomial coefficients
// </vc-preamble>

// <vc-helpers>
function LegendreToMonomialCoeffs(n: nat): seq<real>
  decreases n
{
  if n == 0 then [1.0]
  else if n == 1 then [0.0, 1.0]
  else 
    var prev1 := LegendreToMonomialCoeffs(n-1);
    var prev2 := LegendreToMonomialCoeffs(n-2);
    var factor1 := (2.0 * (n-1) as real + 1.0) / (n as real);
    var factor2 := (n-1) as real / (n as real);
    AddPolynomials(ScaleAndShift(prev1, factor1), ScalePolynomial(prev2, -factor2))
}

function ScalePolynomial(p: seq<real>, scale: real): seq<real>
{
  if |p| == 0 then []
  else [p[0] * scale] + ScalePolynomial(p[1..], scale)
}

function ScaleAndShift(p: seq<real>, scale: real): seq<real>
{
  [0.0] + ScalePolynomial(p, scale)
}

function AddPolynomials(p1: seq<real>, p2: seq<real>): seq<real>
{
  if |p1| == 0 then p2
  else if |p2| == 0 then p1
  else if |p1| < |p2| then [p1[0] + p2[0]] + AddPolynomials(p1[1..], p2[1..])
  else if |p2| < |p1| then [p1[0] + p2[0]] + AddPolynomials(p1[1..], p2[1..])
  else [p1[0] + p2[0]] + AddPolynomials(p1[1..], p2[1..])
}

function PadZeros(p: seq<real>, targetLen: nat): seq<real>
  requires targetLen >= |p|
{
  if |p| == targetLen then p
  else p + [0.0] + PadZeros(p, targetLen - 1)[1..]
}

function AccumulateLegendre(c: seq<real>, index: nat): seq<real>
  requires index <= |c|
  decreases |c| - index
{
  if index >= |c| then if |c| == 0 then [] else PadZeros([], |c|)
  else 
    var mono := LegendreToMonomialCoeffs(index);
    var scaled := ScalePolynomial(mono, c[index]);
    var padded := if |scaled| < |c| then PadZeros(scaled, |c|) else scaled[..|c|];
    var rest := AccumulateLegendre(c, index + 1);
    AddPolynomials(padded, rest)
}
// </vc-helpers>

// <vc-spec>
method leg2poly(c: seq<real>) returns (result: seq<real>)
  requires |c| >= 0
  ensures |result| == |c|
  // For small cases (n < 3), the conversion is identity
  ensures |c| < 3 ==> (forall i :: 0 <= i < |c| ==> result[i] == c[i])
  // The result represents a valid polynomial with the same degree
  ensures |c| > 0 ==> |result| > 0
  // Mathematical relationship: the polynomial represented by result in monomial basis
  // is equivalent to the Legendre series represented by c
  ensures forall x :: EvaluatePolynomial(result, x) == EvaluateLegendre(c, x)
// </vc-spec>
// <vc-code>
{
  if |c| == 0 {
    result := [];
  } else if |c| == 1 {
    result := c;
  } else if |c| == 2 {
    result := c;
  } else {
    result := AccumulateLegendre(c, 0);
  }
}
// </vc-code>
