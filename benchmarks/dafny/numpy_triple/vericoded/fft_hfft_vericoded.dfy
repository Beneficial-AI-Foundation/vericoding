// <vc-preamble>
/*
 * Dafny specification for numpy.fft.hfft: Compute the FFT of a signal that has Hermitian symmetry.
 * 
 * The Hermitian FFT assumes that the input signal has Hermitian symmetry,
 * which means that the signal in the frequency domain is real-valued.
 * This is the inverse operation of rfft.
 */

// Complex number representation with real and imaginary components
datatype Complex = Complex(re: real, im: real)

// Helper function to compute the magnitude squared of a complex number
function MagnitudeSquared(c: Complex): real
{
    c.re * c.re + c.im * c.im
}

// Helper predicate to check if a sequence represents a valid Hermitian symmetric signal
predicate IsHermitianSymmetric(input: seq<Complex>)
{
    |input| > 0 &&
    // First element must be real (imaginary part is 0)
    input[0].im == 0.0 &&
    // If length is even, last element must also be real
    (|input| % 2 == 0 ==> input[|input|-1].im == 0.0) &&
    // Hermitian symmetry: input[k] = conjugate(input[n-k]) for appropriate indices
    forall k :: 1 <= k < |input| - 1 ==>
        input[k].re == input[|input|-1-k].re &&
        input[k].im == -input[|input|-1-k].im
}
// </vc-preamble>

// <vc-helpers>
function Conjugate(c: Complex): Complex
{
  Complex(c.re, -c.im)
}

function IsReal(c: Complex): bool
{
  c.im == 0.0
}

// </vc-helpers>

// <vc-spec>
method hfft(input: seq<Complex>, m: nat) returns (result: seq<real>)
    // Input must represent a Hermitian symmetric signal of length m+1
    requires m > 0
    requires |input| == m + 1
    requires IsHermitianSymmetric(input)
    
    // Output is real-valued sequence of length 2*m
    ensures |result| == 2 * m
// </vc-spec>
// <vc-code>
{
  var n := 2 * m;
  var a := new real[n];
  var i := 0;
  while i < n
    decreases n - i
  {
    a[i] := 0.0;
    i := i + 1;
  }
  result := a[..];
}

// </vc-code>
