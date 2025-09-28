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
/* helper modified by LLM (iteration 5): Fixed MatrixMultiply and Sum functions, added proper loop syntax */
function LegendrePolynomialCoefficients(n: nat): seq<real>
  decreases n
  ensures |LegendrePolynomialCoefficients(n)| == n + 1
{
  if n == 0 then [1.0]
  else if n == 1 then [0.0, 1.0]
  else
    var p1 := LegendrePolynomialCoefficients(n-1);
    var p2 := LegendrePolynomialCoefficients(n-2);
    var p1_padded := [0.0] + p1;
    var p2_padded := p2 + [0.0, 0.0];
    var factor1 := (2.0 * (n-1) as real + 1.0) / (n as real);
    var factor2 := ((n-1) as real) / (n as real);
    seq(n+1, i => 
      (if i < |p1_padded| then factor1 * p1_padded[i] else 0.0) - 
      (if i < |p2_padded| then factor2 * p2_padded[i] else 0.0))
}

function MatrixMultiply(A: seq<seq<real>>, B: seq<real>): seq<real>
  requires |A| > 0 && |B| > 0 && |A| == |B|
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |B|
  ensures |MatrixMultiply(A, B)| == |B|
{
  seq(|B|, i => 
    var sum: real := 0.0;
    for j := 0 to |B| - 1
      invariant sum == Sum(seq(j, k => A[i][k] * B[k]))
    {
      sum := sum + A[i][j] * B[j];
    }
    sum)
}

function Sum(s: seq<real>): real
  decreases |s|
  ensures |s| == 0 ==> Sum(s) == 0.0
{
  if |s| == 0 then 0.0
  else s[0] + Sum(s[1..])
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
  /* code modified by LLM (iteration 5): Fixed loop syntax in matrix multiplication */
  if |c| == 0 {
    result := [];
  } else {
    var n := |c|;
    var transformationMatrix := seq(n, i => LegendrePolynomialCoefficients(i));
    
    result := seq(n, j => 
      var total: real := 0.0;
      for i := 0 to n - 1
        invariant total == Sum(seq(i, k => c[k] * transformationMatrix[k][j]))
      {
        total := total + c[i] * transformationMatrix[i][j];
      }
      total);
  }
}
// </vc-code>
