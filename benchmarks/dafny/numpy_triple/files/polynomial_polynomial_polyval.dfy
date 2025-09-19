// <vc-preamble>
// Helper function to compute power of a real number
function Power(base: real, exp: nat): real
{
    if exp == 0 then 1.0
    else base * Power(base, exp - 1)
}

// Evaluate polynomial at a single point using coefficient array
function EvaluatePolynomial(x: real, coefficients: seq<real>): real
    requires |coefficients| > 0
{
    if |coefficients| == 1 then
        coefficients[0]
    else
        coefficients[0] + x * EvaluatePolynomial(x, coefficients[1..])
}

// Alternative direct polynomial evaluation formula for specification
function PolynomialValue(x: real, coefficients: seq<real>): real
    requires |coefficients| > 0
{
    var n := |coefficients| - 1;
    (seq(n + 1, i requires 0 <= i <= n => coefficients[i] * Power(x, i)))[0] +
    if n > 0 then
        (seq(n, i requires 1 <= i <= n => coefficients[i] * Power(x, i)))[0]
    else 0.0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method polyval(x: seq<real>, c: seq<real>) returns (result: seq<real>)
    requires |c| > 0  // Coefficient array must be non-empty
    ensures |result| == |x|  // Output has same length as input
    ensures forall i :: 0 <= i < |result| ==> 
        result[i] == EvaluatePolynomial(x[i], c)
    ensures |c| == 1 ==> forall i :: 0 <= i < |result| ==> result[i] == c[0]
    ensures (forall j :: 0 <= j < |c| ==> c[j] == 0.0) ==> 
        forall i :: 0 <= i < |result| ==> result[i] == 0.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
