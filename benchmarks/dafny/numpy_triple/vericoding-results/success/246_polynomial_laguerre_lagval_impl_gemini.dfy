// <vc-preamble>
// Ghost function to define the i-th Laguerre polynomial L_i(x)
ghost function LaguerrePolynomial(i: nat, x: real): real
{
    if i == 0 then 1.0
    else if i == 1 then 1.0 - x
    else
        // Recurrence relation: L_n(x) = ((2n-1-x)*L_{n-1}(x) - (n-1)*L_{n-2}(x))/n
        var n := i as real;
        ((2.0*n - 1.0 - x) * LaguerrePolynomial(i-1, x) - (n - 1.0) * LaguerrePolynomial(i-2, x)) / n
}

// Ghost function to evaluate the Laguerre series at a point x
ghost function EvaluateLaguerreSeriesAt(x: real, coefficients: seq<real>): real
{
    if |coefficients| == 0 then 0.0
    else
        // Sum of c_i * L_i(x) for i from 0 to |coefficients|-1
        SumLaguerreTerms(x, coefficients, |coefficients| - 1)
}

// Helper ghost function for recursive summation
ghost function SumLaguerreTerms(x: real, coefficients: seq<real>, degree: nat): real
    requires degree < |coefficients|
{
    if degree == 0 then coefficients[0] * LaguerrePolynomial(0, x)
    else coefficients[degree] * LaguerrePolynomial(degree, x) + SumLaguerreTerms(x, coefficients, degree - 1)
}

/**
 * Evaluates a Laguerre polynomial series at the given points.
 * For each point x[i], computes the value of the polynomial series defined by coefficients.
 */
// </vc-preamble>

// <vc-helpers>
method EvaluateSinglePoint(x_val: real, coeffs: seq<real>) returns (s: real)
  requires |coeffs| > 0
  ensures s == EvaluateLaguerreSeriesAt(x_val, coeffs)
{
  var N := |coeffs|;
  var l_prev := 1.0; // L_0(x)
  s := coeffs[0] * l_prev;

  if N > 1 {
    var l_curr := 1.0 - x_val; // L_1(x)
    s := s + coeffs[1] * l_curr;
    
    var i := 2;
    while i < N
      invariant 2 <= i <= N
      invariant l_prev == LaguerrePolynomial(i-2, x_val)
      invariant l_curr == LaguerrePolynomial(i-1, x_val)
      invariant s == SumLaguerreTerms(x_val, coeffs, i-1)
    {
      var i_real := i as real;
      var l_next := ((2.0 * i_real - 1.0 - x_val) * l_curr - (i_real - 1.0) * l_prev) / i_real;
      s := s + coeffs[i] * l_next;
      l_prev := l_curr;
      l_curr := l_next;
      i := i + 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method LagVal(x: array<real>, coefficients: array<real>) returns (result: array<real>)
    requires x.Length > 0
    requires coefficients.Length > 0
    ensures result.Length == x.Length
    ensures forall i :: 0 <= i < result.Length ==>
        result[i] == EvaluateLaguerreSeriesAt(x[i], coefficients[..])
    ensures fresh(result)
// </vc-spec>
// <vc-code>
{
  result := new real[x.Length];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant fresh(result)
    invariant forall j :: 0 <= j < i ==> result[j] == EvaluateLaguerreSeriesAt(x[j], coefficients[..])
  {
    result[i] := EvaluateSinglePoint(x[i], coefficients[..]);
    i := i + 1;
  }
}
// </vc-code>
