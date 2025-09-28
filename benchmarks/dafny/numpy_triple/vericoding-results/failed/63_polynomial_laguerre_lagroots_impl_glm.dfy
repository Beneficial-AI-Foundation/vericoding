// <vc-preamble>
// Represents the Laguerre polynomial L_i(x) evaluated at x
function LaguerrePolynomial(i: nat, x: real): real
  decreases i
{
  if i == 0 then 1.0
  else if i == 1 then 1.0 - x
  else
    // Recurrence relation: (n+1)L_{n+1}(x) = (2n+1-x)L_n(x) - nL_{n-1}(x)
    var n := i - 1;
    ((2.0 * n as real + 1.0 - x) * LaguerrePolynomial(n, x) - (n as real) * LaguerrePolynomial(n-1, x)) / ((n + 1) as real)
}

// Evaluates the Laguerre series polynomial p(x) = sum_i c[i] * L_i(x)
function EvaluateLaguerrePolynomial(c: seq<real>, x: real): real
  requires |c| > 0
{
  EvaluateLaguerrePolynomialHelper(c, x, 0)
}

function EvaluateLaguerrePolynomialHelper(c: seq<real>, x: real, index: nat): real
  requires |c| > 0
  requires index <= |c|
  decreases |c| - index
{
  if index == |c| then 0.0
  else c[index] * LaguerrePolynomial(index, x) + EvaluateLaguerrePolynomialHelper(c, x, index + 1)
}

// Main method to compute roots of a Laguerre series
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax errors in type annotations */
function EvaluateLaguerrePolynomialDerivative(c: seq<real>, x: real): real
  requires |c| > 0
{
  if |c| == 1 then 0.0
  else
    -c[1] - SumDerivativeTerms(c, x, 2)
}

function SumDerivativeTerms(c: seq<real>, x: real, i: nat): real
  requires 2 <= i <= |c|
  decreases |c| - i
{
  if i == |c| then 0.0
  else
    var s := SumLaguerrePolynomials(x, 0, i-1);
    c[i] * s + SumDerivativeTerms(c, x, i+1)
}

function SumLaguerrePolynomials(x: real, start: nat, end: nat): real
  requires start <= end+1
  decreases end - start
{
  if start > end then 0.0
  else LaguerrePolynomial(start, x) + SumLaguerrePolynomials(x, start+1, end)
}
// </vc-helpers>

// <vc-spec>
method Lagroots(c: seq<real>) returns (roots: seq<real>)
  requires |c| >= 1
  requires c[|c|-1] != 0.0  // Leading coefficient must be non-zero
  ensures |roots| == |c| - 1  // Number of roots equals degree of polynomial
  ensures |c| == 1 ==> |roots| == 0  // Constant polynomial has no finite roots
  ensures |c| == 2 ==> |roots| == 1 && roots[0] == 1.0 + c[0] / c[1]  // Linear case
  ensures forall i :: 0 <= i < |roots| ==> 
    // Each root should make the polynomial evaluate to approximately zero
    var polynomial_value := EvaluateLaguerrePolynomial(c, roots[i]);
    -0.0000000001 <= polynomial_value <= 0.0000000001
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed Newton-Raphson implementation for multiple roots */
{
  if |c| == 1 then
    roots := [];
  else if |c| == 2 then
    roots := [1.0 + c[0] / c[1]];
  else
  {
    roots := [];
    var degree := |c| - 1;
    var i := 0;
    while i < degree
    {
      var x := (i as real + 0.5) * 2.0; // Initial guess
      var iter := 0;
      while iter < 100
      {
        var p := EvaluateLaguerrePolynomial(c, x);
        if |p| <= 0.0000000001 then
          break;
        var dp := EvaluateLaguerrePolynomialDerivative(c, x);
        if dp == 0.0 then
          x := x + 1.0;
        else
          x := x - p / dp;
        iter := iter + 1;
      }
      roots := roots + [x];
      i := i + 1;
    }
  }
}
// </vc-code>
