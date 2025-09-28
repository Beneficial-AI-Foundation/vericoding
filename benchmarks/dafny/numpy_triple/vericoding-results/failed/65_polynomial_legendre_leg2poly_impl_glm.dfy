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
/* helper modified by LLM (iteration 2): added precondition to ensure index safety */
function ConvertLegendreToPolynomialHelper(n: nat, c: seq<real>): seq<real>
  requires n < |c|
{
  if n == 0 then [c[0]]
  else if n == 1 then [c[0], c[1]]
  else
    var prev := ConvertLegendreToPolynomialHelper(n-1, c);
    var prevPrev := ConvertLegendreToPolynomialHelper(n-2, c);
    var current := (2.0 * (n-1) as real + 1.0) / (n as real);
    var prevCoeffs := MultiplyPolynomial(prev, [0.0, current]);
    var prevPrevCoeffs := MultiplyPolynomial(prevPrev, [-(n-1) as real / (n as real)]);
    AddPolynomials(prevCoeffs, prevPrevCoeffs) + [c[n]]
}

function MultiplyPolynomial(p: seq<real>, q: seq<real>): seq<real>
{
  if |p| == 0 then []
  else if |q| == 0 then []
  else
    [p[0] * q[0]] +
    AddPolynomials(
      MultiplyPolynomial(p, q[1..]),
      MultiplyPolynomial(p[1..], q)
    )
}

function AddPolynomials(p: seq<real>, q: seq<real>): seq<real>
{
  if |p| == 0 then q
  else if |q| == 0 then p
  else [p[0] + q[0]] + AddPolynomials(p[1..], q[1..])
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
/* code modified by LLM (iteration 3): fixed compilation error by using block if syntax without then keyword */
{
  if |c| == 0 {
    result := [];
  } else if |c| == 1 {
    result := [c[0]];
  } else if |c| == 2 {
    result := [c[0], c[1]];
  } else {
    result := ConvertLegendreToPolynomialHelper(|c|-1, c);
  }
}
// </vc-code>
