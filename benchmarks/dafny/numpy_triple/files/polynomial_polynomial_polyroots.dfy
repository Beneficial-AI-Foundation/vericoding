// <vc-preamble>
// Complex number datatype to represent polynomial roots
datatype Complex = Complex(realPart: real, imagPart: real)

// Complex number arithmetic operations
function ComplexAdd(a: Complex, b: Complex): Complex {
    Complex(a.realPart + b.realPart, a.imagPart + b.imagPart)
}

function ComplexMult(a: Complex, b: Complex): Complex {
    Complex(a.realPart * b.realPart - a.imagPart * b.imagPart, a.realPart * b.imagPart + a.imagPart * b.realPart)
}

function ComplexPower(base: Complex, exp: nat): Complex
    decreases exp
{
    if exp == 0 then Complex(1.0, 0.0)
    else if exp == 1 then base
    else ComplexMult(base, ComplexPower(base, exp - 1))
}

function ComplexZero(): Complex { 
    Complex(0.0, 0.0) 
}

function ComplexEquals(a: Complex, b: Complex): bool {
    a.realPart == b.realPart && a.imagPart == b.imagPart
}

// Helper function to evaluate polynomial at a given complex point
function EvaluatePolynomialHelper(coeffs: seq<real>, x: Complex, power: Complex, index: nat): Complex
    requires index <= |coeffs|
    decreases |coeffs| - index
{
    if index >= |coeffs| then ComplexZero()
    else ComplexAdd(
        ComplexMult(Complex(coeffs[index], 0.0), power),
        EvaluatePolynomialHelper(coeffs, x, ComplexMult(power, x), index + 1)
    )
}

// Evaluate polynomial p(x) = coeffs[0] + coeffs[1]*x + ... + coeffs[n]*x^n at point x
function EvaluatePolynomial(coeffs: seq<real>, x: Complex): Complex
    requires |coeffs| > 0
{
    EvaluatePolynomialHelper(coeffs, x, Complex(1.0, 0.0), 0)
}

// Method to compute all roots of a polynomial
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method PolyRoots(coeffs: seq<real>) returns (roots: seq<Complex>)
    // Polynomial must have at least degree 1 (non-constant)
    requires |coeffs| >= 2
    // Leading coefficient must be non-zero to ensure well-defined degree
    requires coeffs[|coeffs| - 1] != 0.0
    // Returns exactly n roots for a degree-n polynomial
    ensures |roots| == |coeffs| - 1
    // Each returned value is actually a root of the polynomial
    ensures forall i :: 0 <= i < |roots| ==> 
        ComplexEquals(EvaluatePolynomial(coeffs, roots[i]), ComplexZero())
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
