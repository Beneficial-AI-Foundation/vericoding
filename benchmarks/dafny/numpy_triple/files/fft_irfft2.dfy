// <vc-preamble>
// Complex number datatype for frequency domain input
datatype Complex = Complex(re: real, im: real)

// Method that computes the inverse 2D real FFT of a 2D array
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_irfft2(a: array2<Complex>) returns (result: array2<real>)
  
  // Postconditions: ensure proper matrix structure and transformation properties
  
  // Preserve matrix dimensions - same number of rows and columns
  ensures result.Length0 == a.Length0
  ensures result.Length1 == a.Length1
  
  // Non-trivial transformation: if input contains non-zero elements, 
  // then output contains non-zero elements (preserves information content)
  ensures (exists i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 && (a[i, j].re != 0.0 || a[i, j].im != 0.0)) ==>
          (exists k, l :: 0 <= k < result.Length0 && 0 <= l < result.Length1 && result[k, l] != 0.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
