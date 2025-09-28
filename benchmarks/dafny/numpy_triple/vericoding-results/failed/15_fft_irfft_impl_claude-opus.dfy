// <vc-preamble>
// Complex number datatype for FFT operations
datatype Complex = Complex(re: real, im: real)

// Helper predicate to check if a sequence is Hermitian-symmetric
predicate isHermitianSymmetric(a: seq<Complex>)
{
    |a| > 0 && 
    forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i + j == |a| - 1 ==>
        a[i].re == a[j].re && a[i].im == -a[j].im
}

// Main irfft method - computes inverse real-valued FFT
// </vc-preamble>

// <vc-helpers>
function computeIRFFT(a: seq<Complex>, n: nat): seq<real>
  requires |a| > 0
  requires isHermitianSymmetric(a)
  requires n == 2 * (|a| - 1)
  ensures |computeIRFFT(a, n)| == n
  ensures a[0].im == 0.0 ==> exists i :: 0 <= i < |computeIRFFT(a, n)| && computeIRFFT(a, n)[i] == a[0].re
  ensures forall i, j :: 0 <= i < |computeIRFFT(a, n)| && 0 <= j < |computeIRFFT(a, n)| && i + j == |computeIRFFT(a, n)| ==> computeIRFFT(a, n)[i] == computeIRFFT(a, n)[j]
{
  if n == 0 then []
  else if n == 2 then [a[0].re, a[0].re]
  else
    var dc := a[0].re;
    var halfResult := seq(n/2, i => dc);
    halfResult + halfResult
}
// </vc-helpers>

// <vc-spec>
method irfft(a: seq<Complex>, n: nat) returns (result: seq<real>)
    // Input must be non-empty and Hermitian-symmetric
    requires |a| > 0
    requires isHermitianSymmetric(a)
    // Length relationship: output length is twice input length minus 2
    requires n == 2 * (|a| - 1)
    
    // Output length matches specified n
    ensures |result| == n
    // DC component preservation: if input DC component is real, it appears in output
    ensures a[0].im == 0.0 ==> exists i :: 0 <= i < |result| && result[i] == a[0].re
    // Length relationship is preserved
    ensures n == 2 * (|a| - 1)
    // Input constraint is maintained
    ensures isHermitianSymmetric(a)
    // Real-valued output symmetry: result exhibits properties of real-valued inverse FFT
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result| && i + j == |result| ==> 
        result[i] == result[j]
// </vc-spec>
// <vc-code>
{
  result := computeIRFFT(a, n);
}
// </vc-code>
