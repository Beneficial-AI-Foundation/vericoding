// <vc-preamble>
/*
 * Chebyshev polynomial generation from roots.
 * 
 * This module generates Chebyshev series coefficients for polynomials with given roots.
 * Given a set of roots r₀, r₁, ..., rₙ₋₁, it computes coefficients c₀, c₁, ..., cₙ
 * such that the polynomial p(x) = (x - r₀) * (x - r₁) * ... * (x - rₙ₋₁)
 * can be expressed as p(x) = c₀ + c₁ * T₁(x) + ... + cₙ * Tₙ(x)
 * where Tₖ(x) is the k-th Chebyshev polynomial of the first kind.
 */

// Evaluate the k-th Chebyshev polynomial of the first kind at x
function EvalChebyshevT(k: nat, x: real): real
{
    if k == 0 then 1.0
    else if k == 1 then x
    else 2.0 * x * EvalChebyshevT(k - 1, x) - EvalChebyshevT(k - 2, x)
}

// Evaluate a polynomial in Chebyshev basis at point x given coefficients
function EvalChebyshevPoly(coeffs: seq<real>, x: real): real
{
    if |coeffs| == 0 then 0.0
    else SumChebyshevTerms(coeffs, x, 0)
}

// Helper function to sum Chebyshev terms recursively
function SumChebyshevTerms(coeffs: seq<real>, x: real, i: nat): real
    requires i <= |coeffs|
    decreases |coeffs| - i
{
    if i == |coeffs| then 0.0
    else coeffs[i] * EvalChebyshevT(i, x) + SumChebyshevTerms(coeffs, x, i + 1)
}

// Power function for real numbers
function Pow(base: real, exp: int): real
{
    if exp == 0 then 1.0
    else if exp > 0 then base * Pow(base, exp - 1)
    else 1.0 / Pow(base, -exp)
}

// Generate Chebyshev series coefficients from given roots
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ChebFromRoots(roots: seq<real>) returns (coeffs: seq<real>)
    ensures |coeffs| == |roots| + 1
    // For each root r, evaluating the Chebyshev polynomial at r gives zero
    ensures forall i :: 0 <= i < |roots| ==> EvalChebyshevPoly(coeffs, roots[i]) == 0.0
    // The highest degree coefficient is non-zero when there are roots
    ensures |roots| > 0 ==> coeffs[|roots|] != 0.0
    // The leading coefficient has the specific mathematical relationship for Chebyshev basis
    ensures |roots| > 0 ==> coeffs[|roots|] == Pow(2.0, 1 - |roots|)
    // The polynomial represented by coeffs has exactly the given roots
    // (implicitly satisfied by the zero-evaluation property above)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
