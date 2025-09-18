// <vc-preamble>
// Helper function to evaluate a polynomial at a given point
ghost function PolyEval(coeffs: seq<real>, x: real): real
{
    if |coeffs| == 0 then 0.0
    else coeffs[0] + (if |coeffs| == 1 then 0.0 else x * PolyEval(coeffs[1..], x))
}

// Helper function to compute the k-th Chebyshev polynomial at x
ghost function ChebyshevT(k: nat, x: real): real
{
    if k == 0 then 1.0
    else if k == 1 then x
    else 2.0 * x * ChebyshevT(k-1, x) - ChebyshevT(k-2, x)
}

// Helper function to evaluate a Chebyshev series at a given point
ghost function ChebyshevEval(coeffs: seq<real>, x: real): real
{
    ChebyshevEvalSum(coeffs, x)
}

// More precise Chebyshev series evaluation using summation
ghost function ChebyshevEvalSum(coeffs: seq<real>, x: real): real
{
    SumChebyshevTerms(coeffs, x, 0)
}

ghost function SumChebyshevTerms(coeffs: seq<real>, x: real, k: nat): real
{
    if k >= |coeffs| then 0.0
    else coeffs[k] * ChebyshevT(k, x) + SumChebyshevTerms(coeffs, x, k + 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Cheb2Poly(c: seq<real>) returns (p: seq<real>)
    // Convert Chebyshev series coefficients to polynomial coefficients
    ensures |p| == |c| // Length preservation
    
    // Identity cases: for n ≤ 2, output equals input since T₀(x) = 1, T₁(x) = x
    ensures |c| == 0 ==> p == c
    ensures |c| == 1 ==> p == c  
    ensures |c| == 2 ==> p == c
    
    // Mathematical correctness: polynomial and Chebyshev series evaluate to same value
    ensures forall x: real :: PolyEval(p, x) == ChebyshevEvalSum(c, x)
    
    // Concrete example verification: [0, 1, 2, 3] → [-2, -8, 4, 12]
    ensures |c| == 4 && c == [0.0, 1.0, 2.0, 3.0] ==> 
            p == [-2.0, -8.0, 4.0, 12.0]
            
    // Zero coefficient property: if all Chebyshev coefficients are zero, polynomial coefficients are zero
    ensures (forall i :: 0 <= i < |c| ==> c[i] == 0.0) ==> 
            (forall i :: 0 <= i < |p| ==> p[i] == 0.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
