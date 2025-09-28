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
/* helper modified by LLM (iteration 5): Fixed syntax by adding return statement in function body to resolve compilation errors and ensure proper type inference for ensured properties. */
function MonomialCoeffs(n: nat): seq<real>
  decreases n
  ensures |result| == n + 1
  ensures forall x :: EvaluatePolynomial(result, x) == LegendrePolynomial(n, x)
{
  if n == 0 then [1.0]
  else if n == 1 then [0.0, 1.0]
  else
    var a := (2.0 * (n-1) as real + 1.0) / n as real;
    var b := ((n-1) as real) / n as real;
    var c1 := MonomialCoeffs(n-1);
    var c2 := MonomialCoeffs(n-2);
    return seq(n+1, i => a * (if i >= 1 then c1[i-1] else 0.0) - b * (if i < |c2| then c2[i] else 0.0));
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
/* code modified by LLM (iteration 5): Implemented iteration to compute sum of monomial coefficients for each Legendre term with updated helper function call. */
{
  var n := |c|;
  if n == 0 {
    result := [];
  } else {
    var poly := seq(n, i => 0.0);
    for k := 0 to n - 1
    {
      var coeffs := MonomialCoeffs(k);
      for j := 0 to k
      {
        poly := poly[j := poly[j] + c[k] * coeffs[j]];
      }
    }
    result := poly;
  }
}
// </vc-code>
