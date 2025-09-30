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
    invariant forall j :: 0 <= j < i ==> result[j] == EvaluateLaguerreSeriesAt(x[j], coefficients[..])
  {
    var xi := x[i];
    var sum := 0.0;
    
    if coefficients.Length >= 1 {
      var L0 := 1.0;
      sum := coefficients[0] * L0;
      
      if coefficients.Length >= 2 {
        var L1 := 1.0 - xi;
        sum := sum + coefficients[1] * L1;
        
        var k := 2;
        var Lk_minus_2 := L0;
        var Lk_minus_1 := L1;
        
        while k < coefficients.Length
          invariant 2 <= k <= coefficients.Length
          invariant Lk_minus_2 == LaguerrePolynomial(k-2, xi)
          invariant Lk_minus_1 == LaguerrePolynomial(k-1, xi)
          invariant sum == SumLaguerreTerms(xi, coefficients[..], k-1)
        {
          var n := k as real;
          var Lk := ((2.0*n - 1.0 - xi) * Lk_minus_1 - (n - 1.0) * Lk_minus_2) / n;
          sum := sum + coefficients[k] * Lk;
          
          Lk_minus_2 := Lk_minus_1;
          Lk_minus_1 := Lk;
          k := k + 1;
        }
      }
    }
    
    result[i] := sum;
    i := i + 1;
  }
}
// </vc-code>
