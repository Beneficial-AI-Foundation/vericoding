// <vc-preamble>
// Helper function to evaluate a standard polynomial
function StandardPolynomialEval(coeffs: seq<real>, x: real): real
{
  if |coeffs| == 0 then 0.0
  else if |coeffs| == 1 then coeffs[0]
  else coeffs[0] + x * StandardPolynomialEval(coeffs[1..], x)
}

// Helper function to compute the i-th Laguerre polynomial L_i(x)
function LaguerrePolynomial(n: nat, x: real): real
  decreases n
{
  if n == 0 then 1.0
  else if n == 1 then 1.0 - x
  else ((2.0 * n as real - 1.0 - x) * LaguerrePolynomial(n-1, x) - (n as real - 1.0) * LaguerrePolynomial(n-2, x)) / (n as real)
}

// Helper function to evaluate a Laguerre series
function LaguerreSeriesEval(coeffs: seq<real>, x: real): real
{
  if |coeffs| == 0 then 0.0
  else if |coeffs| == 1 then coeffs[0] * LaguerrePolynomial(0, x)
  else coeffs[0] * LaguerrePolynomial(0, x) + LaguerreSeriesEval(coeffs[1..], x)
}

// More precise Laguerre series evaluation using explicit summation
function LaguerreSeriesEvalExact(coeffs: seq<real>, x: real): real
{
  SumLaguerreTerms(coeffs, x, 0)
}

function SumLaguerreTerms(coeffs: seq<real>, x: real, i: nat): real
  requires i <= |coeffs|
  decreases |coeffs| - i
{
  if i == |coeffs| then 0.0
  else coeffs[i] * LaguerrePolynomial(i, x) + SumLaguerreTerms(coeffs, x, i+1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed incomplete helper function based on compilation errors. */
// </vc-helpers>

// <vc-spec>
method Poly2Lag(pol: seq<real>) returns (result: seq<real>)
  ensures |result| == |pol|
  ensures forall x: real :: StandardPolynomialEval(pol, x) == LaguerreSeriesEvalExact(result, x)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed compilation error by adding braces to 'if n == 0' statement. This was a syntax error. */
{
  var n := |pol|;
  if n == 0 then {
    return [];
  }
  else if n == 1 then {
    return [pol[0]];
  }
  else {
    var res := new real[n];
    var C := new real[n];

    for k := 0 to n - 1
      invariant 0 <= k < n
      invariant forall j: nat | 0 <= j <= k :: C[j] == pol[n-1-j]
    {
      C[k] := pol[n-1-k];
    }

    for k := 0 to n - 1
      invariant 0 <= k < n
      invariant forall j: nat | 0 <= j < k :: res[n-1-j] == C[j]
    {
      var c_k := C[k];
      res[n-1-k] := c_k;
      for i := k + 1 to n - 1
        invariant k+1 <= i <= n
        invariant forall j: nat | k < j < i :: C[j] == pol[n-1-j]
        invariant C[i] == pol[n-1-i] + (i as real + 1.0) * c_k
      {
        C[i] := C[i] + ((i as real) + 1.0) * c_k;
      }
    }
    return res;
  }
}
// </vc-code>
