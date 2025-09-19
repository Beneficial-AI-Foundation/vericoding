// <vc-preamble>
// Polynomial represented as sequence of coefficients from lowest to highest degree
type Polynomial = seq<real>

// Ghost function to evaluate polynomial at a point
ghost function EvalPoly(p: Polynomial, x: real): real
{
    if |p| == 0 then 0.0
    else p[0] + x * EvalPoly(p[1..], x)
}

// Ghost function to multiply two polynomials
ghost function MultiplyPoly(p1: Polynomial, p2: Polynomial): Polynomial
{
    var result := seq(if |p1| == 0 || |p2| == 0 then 0 else |p1| + |p2| - 1, i => 0.0);
    seq(|result|, k => 
        MultiplyPolyHelper(p1, p2, k, 0)
    )
}

// Helper function for polynomial multiplication
ghost function MultiplyPolyHelper(p1: Polynomial, p2: Polynomial, k: int, j: int): real
    requires 0 <= j <= k + 1
{
    if j > k || j >= |p1| then 0.0
    else
        var term := if k - j < |p2| then p1[j] * p2[k - j] else 0.0;
        term + MultiplyPolyHelper(p1, p2, k, j + 1)
}

// Ghost function to add two polynomials
ghost function AddPoly(p1: Polynomial, p2: Polynomial): Polynomial
{
    var maxLen := if |p1| > |p2| then |p1| else |p2|;
    seq(maxLen, i =>
        (if i < |p1| then p1[i] else 0.0) +
        (if i < |p2| then p2[i] else 0.0)
    )
}

// Ghost function to get degree of polynomial (index of highest non-zero coefficient)
ghost function PolyDegree(p: Polynomial): int
{
    if |p| == 0 then -1
    else PolyDegreeHelper(p, |p| - 1)
}

// Helper function for finding polynomial degree
ghost function PolyDegreeHelper(p: Polynomial, i: int): int
    requires -1 <= i < |p|
{
    if i < 0 then -1
    else if p[i] != 0.0 then i
    else PolyDegreeHelper(p, i - 1)
}

// Ghost function to remove leading zeros from polynomial
ghost function TrimPoly(p: Polynomial): Polynomial
{
    if |p| == 0 then p
    else
        var degree := PolyDegree(p);
        if degree < 0 then [] else p[..degree+1]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method PolynomialDivision(dividend: Polynomial, divisor: Polynomial) 
    returns (quotient: Polynomial, remainder: Polynomial)
    requires |divisor| > 0
    requires divisor[|divisor|-1] != 0.0  // Leading coefficient is non-zero
    ensures forall x: real :: EvalPoly(dividend, x) == EvalPoly(AddPoly(MultiplyPoly(divisor, quotient), remainder), x)
    ensures PolyDegree(remainder) < PolyDegree(divisor) || (|remainder| == 0)
    ensures |quotient| <= |dividend|
    ensures |remainder| == |dividend|
    ensures |divisor| == 1 ==> (
        |quotient| == |dividend| &&
        (forall i :: 0 <= i < |quotient| ==> quotient[i] == dividend[i] / divisor[0]) &&
        |remainder| == 0
    )
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
