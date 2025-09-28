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
/* helper modified by LLM (iteration 5): Fixed while loop syntax and improved implementation for converting standard poly to Laguerre coefficients */
function Poly2LagHelper(pol: seq<real>, n: nat): real
  requires n < |pol|
  decreases |pol| - n
{
  if n >= |pol| then 0.0
  else {
    var sum := 0.0;
    var k := n;
    while k < |pol|
      invariant k >= n
      decreases |pol| - k
    {
      sum := sum + pol[k] * BinomialCoefficient(k, n);
      k := k + 1;
    }
    sum
  }
}

function BinomialCoefficient(n: nat, k: nat): real
  requires 0 <= k <= n
  decreases n - k
{
  if k == 0 || k == n then 1.0
  else BinomialCoefficient(n-1, k-1) + BinomialCoefficient(n-1, k)
}
// </vc-helpers>

// <vc-spec>
method Poly2Lag(pol: seq<real>) returns (result: seq<real>)
  ensures |result| == |pol|
  ensures forall x: real :: StandardPolynomialEval(pol, x) == LaguerreSeriesEvalExact(result, x)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed sequence construction and while loop implementation */
{
  result := [];
  var i := 0;
  while i < |pol|
    invariant i >= 0
    decreases |pol| - i
  {
    result := result + [Poly2LagHelper(pol, i)];
    i := i + 1;
  }
}
// </vc-code>
