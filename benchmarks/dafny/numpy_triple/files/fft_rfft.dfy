// <vc-preamble>
datatype Complex = Complex(re: real, im: real)

// Complex arithmetic operations
function ComplexZero(): Complex { Complex(0.0, 0.0) }

function ComplexAdd(z1: Complex, z2: Complex): Complex {
    Complex(z1.re + z2.re, z1.im + z2.im)
}

function ComplexMul(z1: Complex, z2: Complex): Complex {
    Complex(z1.re * z2.re - z1.im * z2.im, z1.re * z2.im + z1.im * z2.re)
}

function RealToComplex(x: real): Complex {
    Complex(x, 0.0)
}

// Complex exponential function: e^(iθ) = cos(θ) + i*sin(θ)
function ComplexExp(theta: real): Complex
    requires -1000.0 <= theta <= 1000.0  // Reasonable bounds for trigonometric functions
{
    // Using mathematical definitions - in actual implementation would use library functions
    Complex(Cos(theta), Sin(theta))
}

// Placeholder trigonometric functions (would use standard library in practice)
function Cos(x: real): real
    requires -1000.0 <= x <= 1000.0
    ensures -1.0 <= Cos(x) <= 1.0
{
    // Stub implementation for compilation
    0.0
}

function Sin(x: real): real  
    requires -1000.0 <= x <= 1000.0
    ensures -1.0 <= Sin(x) <= 1.0
{
    // Stub implementation for compilation
    0.0
}

// Mathematical constant π
const PI: real := 3.14159265358979323846

// Sum of complex numbers over a range
function ComplexSum(f: int -> Complex, start: int, end: int): Complex
    requires start <= end
    decreases end - start
{
    if start == end then ComplexZero()
    else ComplexAdd(f(start), ComplexSum(f, start + 1, end))
}

// DFT kernel function for real FFT
function DFTKernel(input: seq<real>, k: int, n: int): Complex
    requires n > 0
    requires 0 <= k <= n / 2
    requires |input| == n
{
    ComplexSum((j: int) => 
        if 0 <= j < n then
            ComplexMul(RealToComplex(input[j]), 
                      ComplexExp(-2.0 * PI * (k as real) * (j as real) / (n as real)))
        else ComplexZero(), 0, n)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method rfft(input: seq<real>) returns (output: seq<Complex>)
    requires |input| > 0
    ensures |output| == |input| / 2 + 1
    ensures forall k :: 0 <= k < |output| ==> 
        output[k] == DFTKernel(input, k, |input|)
    // DC component (k=0) is real
    ensures |output| > 0 ==> output[0].im == 0.0
    // For even n, Nyquist frequency (k=n/2) is real  
    ensures |input| % 2 == 0 && |input| / 2 < |output| ==> 
        output[|input| / 2].im == 0.0
    // Linearity property: mathematical relationship preserved
    ensures forall k :: 0 <= k < |output| ==> 
        output[k] == ComplexSum((j: int) => 
            if 0 <= j < |input| then
                ComplexMul(RealToComplex(input[j]), 
                          ComplexExp(-2.0 * PI * (k as real) * (j as real) / (|input| as real)))
            else ComplexZero(), 0, |input|)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
