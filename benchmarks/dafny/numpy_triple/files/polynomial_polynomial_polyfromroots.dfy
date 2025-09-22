// <vc-preamble>
// Helper function to evaluate a polynomial given coefficients and input value
ghost function EvaluatePolynomial(coeffs: seq<real>, x: real): real
{
    if |coeffs| == 0 then 0.0
    else coeffs[0] + x * EvaluatePolynomial(coeffs[1..], x)
}

// Helper function to compute x raised to the power n
ghost function Power(x: real, n: nat): real
{
    if n == 0 then 1.0
    else x * Power(x, n - 1)
}

// Alternative polynomial evaluation using explicit powers
ghost function EvaluatePolynomialExplicit(coeffs: seq<real>, x: real): real
{
    if |coeffs| == 0 then 0.0
    else SumTerms(coeffs, x, 0)
}

// Helper function to sum all polynomial terms
ghost function SumTerms(coeffs: seq<real>, x: real, i: nat): real
{
    if i >= |coeffs| then 0.0
    else coeffs[i] * Power(x, i) + SumTerms(coeffs, x, i + 1)
}

// Main method to generate monic polynomial from roots
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method PolynomialFromRoots(roots: seq<real>) returns (coeffs: seq<real>)
    // Input can be any sequence of real numbers representing roots
    requires true
    
    // Output specifications
    ensures |coeffs| == |roots| + 1
    
    // The polynomial is monic (leading coefficient is 1)
    ensures |coeffs| > 0 ==> coeffs[|coeffs| - 1] == 1.0
    
    // For each root r in the input, the polynomial evaluates to zero at r
    ensures forall r :: r in roots ==> EvaluatePolynomial(coeffs, r) == 0.0
    
    // The polynomial has the correct degree (non-zero leading coefficient when degree > 0)
    ensures |roots| > 0 ==> |coeffs| > 0 && coeffs[|coeffs| - 1] != 0.0
    
    // When there are no roots, return the constant polynomial 1
    ensures |roots| == 0 ==> coeffs == [1.0]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
