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
/* helper modified by LLM (iteration 3): Helpers for computing Laguerre polynomial coefficients and polynomial operations */
function LaguerreCoeffs(n: nat): seq<real>
{
  if n == 0 then [1.0]
  else if n == 1 then [1.0, -1.0]
  else
    var nReal := n as real;
    var L_prev := LaguerreCoeffs(n-1);
    var L_prev2 := LaguerreCoeffs(n-2);
    var constant := 2.0 * nReal - 1.0;
    var minusX_L_prev := MultiplySequence(-1.0, MultiplyByX(L_prev));
    var term1 := AddSequences(MultiplySequence(constant, L_prev), minusX_L_prev);
    var term2 := MultiplySequence(-(n-1) as real, L_prev2);
    var inner := AddSequences(term1, term2);
    MultiplySequence(1.0 / nReal, inner)
}

function MultiplyByX(a: seq<real>): seq<real>
{
  [0.0] + a
}

function AddSequences(a: seq<real>, b: seq<real>): seq<real>
{
  var len := if |a| > |b| then |a| else |b|;
  var p := a + seq(len - |a|, i => 0.0);
  var q := b + seq(len - |b|, i => 0.0);
  seq(len, i => p[i] + q[i])
}

function MultiplySequence(s: real, a: seq<real>): seq<real>
{
  seq(|a|, i => s * a[i])
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
  /* code modified by LLM (iteration 3): Implemented Laguerre series to polynomial conversion using array for accumulation */
  var r : array<real> := new real[|c|](_ => 0.0);
  for k : int := 0 to |c|-1
  {
    var coeffs := LaguerreCoeffs(k);
    var scaled := MultiplySequence(c[k], coeffs);
    for i : int := 0 to |scaled|-1
    {
      r[i] := r[i] + scaled[i];
    }
  }
  result := r[..];
}
// </vc-code>
