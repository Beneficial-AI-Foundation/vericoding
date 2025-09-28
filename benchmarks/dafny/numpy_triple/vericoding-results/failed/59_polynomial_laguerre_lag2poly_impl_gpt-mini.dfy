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
/* helper modified by LLM (iteration 5): pad sequence to length m (right) */
function PadRight(a: seq<real>, m: nat): seq<real>
  decreases m
  ensures |result| == m
{
  if m == 0 then
    []
  else if |a| == 0 then
    [0.0] + PadRight([], m - 1)
  else
    [a[0]] + PadRight(a[1..], m - 1)
}

/* helper modified by LLM (iteration 5): element-wise addition of polynomials (handles different lengths) */
function PolyAdd(a: seq<real>, b: seq<real>): seq<real>
  decreases |a| + |b|
  ensures |result| == (if |a| >= |b| then |a| else |b|)
{
  if |a| == 0 then b
  else if |b| == 0 then a
  else [a[0] + b[0]] + PolyAdd(a[1..], b[1..])
}

/* helper modified by LLM (iteration 5): scalar multiplication of polynomial */
function ScalarMul(a: seq<real>, k: real): seq<real>
  decreases |a|
  ensures |result| == |a|
{
  if |a| == 0 then
    []
  else
    [a[0] * k] + ScalarMul(a[1..], k)
}

/* helper modified by LLM (iteration 5): multiply polynomial by x (shift coefficients right) */
function PolyMulX(a: seq<real>): seq<real>
  ensures |result| == |a| + 1
{
  [0.0] + a
}

/* helper modified by LLM (iteration 5): compute coefficients of nth Laguerre polynomial */
function LaguerrePolyCoeffs(n: nat): seq<real>
  decreases n
  ensures |result| == n + 1
{
  if n == 0 then
    [1.0]
  else if n == 1 then
    [1.0, -1.0]
  else
    var prev := LaguerrePolyCoeffs(n - 1);
    var prev2 := LaguerrePolyCoeffs(n - 2);
    var term1 := ScalarMul(prev, (2.0 * n as real - 1.0) / (n as real));
    var term2 := ScalarMul(PolyMulX(prev), -1.0 / (n as real));
    var term3 := ScalarMul(prev2, -((n as real - 1.0) / (n as real)));
    var t1 := PadRight(term1, n + 1);
    var t2 := PadRight(term2, n + 1);
    var t3 := PadRight(term3, n + 1);
    PolyAdd(PolyAdd(t1, t2), t3)
}

/* helper modified by LLM (iteration 5): convert a Laguerre series to polynomial coefficients */
function LaguerreSeriesToPoly(c: seq<real>): seq<real>
  requires |c| > 0
  decreases |c|
  ensures |result| == |c|
{
  if |c| == 1 then
    [c[0]]
  else
    var prev := LaguerreSeriesToPoly(c[..|c|-1]);
    var coeffs := LaguerrePolyCoeffs(|c| - 1);
    var contrib := ScalarMul(coeffs, c[|c| - 1]);
    PolyAdd(PadRight(prev, |c|), contrib)
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
  /* code modified by LLM (iteration 5): compute polynomial coefficients from Laguerre series */
  result := LaguerreSeriesToPoly(c);
}

// </vc-code>
