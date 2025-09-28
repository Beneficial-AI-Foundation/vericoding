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
/* helper modified by LLM (iteration 5): Removed unnecessary helper, as the code can directly compute the Legendre polynomial coefficients during the main method execution. This avoids redundant functional calls and simplifies the overall implementation by integrating this logic directly into the method's loops. */
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
/* code modified by LLM (iteration 5): Corrected array initialization syntax. */
{
  var n := |c|;
  if n == 0 {
    return [];
  }

  var polyCoeffs: array<real>;
  polyCoeffs := new real[n];

  for i := 0 to n - 1 {
    polyCoeffs[i] := 0.0;
  }

  // S[m][k] will store the coefficient of x^k in Legendre polynomial P_m(x)
  var S: array<array<real>> := new array<array<real>>(n, j => new real[n]);

  for i := 0 to n - 1 {
       for j := 0 to n - 1 {
            S[i][j] := 0.0;
        }
  }

  S[0][0] := 1.0; // P_0(x) = 1
  if n > 1 {
    S[1][1] := 1.0; // P_1(x) = x
  }

  // Compute S[m][k] using recurrence relation for Legendre polynomials coefficients
  // m is the degree of the Legendre polynomial and k is the power of x
  for m := 2 to n - 1 {
    for k := 0 to m {
        var term1: real;
        if k > 0 {
            // (2m-1)/m * P_{m-1}(x) * x term
            term1 := ((2.0 * m as real - 1.0) / m as real) * S[m-1][k-1];
        } else {
            term1 := 0.0;
        }

        var term2: real;
        // (m-1)/m * P_{m-2}(x) term
        term2 := ((m as real - 1.0) / m as real) * S[m-2][k];

        S[m][k] := term1 - term2;
    }
  }

  // Combine Legendre series coefficients with monomial coefficients
  for i := 0 to n - 1 {
    for j := 0 to n - 1 {
      if j <= i {
        polyCoeffs[j] := polyCoeffs[j] + c[i] * S[i][j];
      }
    }
  }

  result := polyCoeffs[0..];
}
// </vc-code>
