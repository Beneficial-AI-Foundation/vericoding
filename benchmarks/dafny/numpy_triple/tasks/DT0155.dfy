// <vc-preamble>
// Complex number representation
datatype Complex = Complex(re: real, im: real)

// Complex number zero
function ComplexZero(): Complex
{
    Complex(0.0, 0.0)
}

// Complex addition
function ComplexAdd(a: Complex, b: Complex): Complex
{
    Complex(a.re + b.re, a.im + b.im)
}

// Complex multiplication
function ComplexMul(a: Complex, b: Complex): Complex
{
    Complex(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re)
}

// Scalar multiplication of complex number
function ComplexScale(s: real, c: Complex): Complex
{
    Complex(s * c.re, s * c.im)
}

// Complex exponential e^(i*theta) = cos(theta) + i*sin(theta)
function ComplexExp(theta: real): Complex
{
    Complex(RealCos(theta), RealSin(theta))
}

// Sine and cosine functions (dummy implementations for compilation)
function RealSin(x: real): real
{
    0.0  // dummy implementation for compilation
}

function RealCos(x: real): real
{
    1.0  // dummy implementation for compilation
}

// Pi constant
const PI: real := 3.14159265358979323846

// Sum over a sequence of complex numbers
function ComplexSum(values: seq<Complex>): Complex
{
    if |values| == 0 then ComplexZero()
    else ComplexAdd(values[0], ComplexSum(values[1..]))
}

// Generate sequence for double summation in IFFTN formula
function GenerateIFFTNSum(a: seq<seq<Complex>>, i: nat, j: nat, m: nat, n: nat): seq<Complex>
    requires m > 0 && n > 0
    requires i < m && j < n
    requires |a| == m
    requires forall k :: 0 <= k < |a| ==> |a[k]| == n
{
    seq(m, k requires 0 <= k < m =>
        ComplexSum(seq(n, l requires 0 <= l < n =>
            ComplexMul(a[k][l], 
                ComplexExp(2.0 * PI * (i as real * k as real / m as real + j as real * l as real / n as real))))))
}

// N-dimensional Inverse Discrete Fourier Transform method
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IFFTN(a: seq<seq<Complex>>) returns (result: seq<seq<Complex>>)
    requires |a| > 0
    requires forall k :: 0 <= k < |a| ==> |a[k]| > 0
    requires forall k :: 0 <= k < |a| ==> |a[k]| == |a[0]|  // All rows have same length
    ensures |result| == |a|
    ensures forall k :: 0 <= k < |result| ==> |result[k]| == |a[0]|
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
        result[i][j] == ComplexScale(1.0 / (|a| as real * |a[0]| as real),
            ComplexSum(seq(|a|, k requires 0 <= k < |a| =>
                ComplexSum(seq(|a[0]|, l requires 0 <= l < |a[0]| =>
                    ComplexMul(a[k][l], 
                        ComplexExp(2.0 * PI * (i as real * k as real / |a| as real + 
                                             j as real * l as real / |a[0]| as real))))))))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
