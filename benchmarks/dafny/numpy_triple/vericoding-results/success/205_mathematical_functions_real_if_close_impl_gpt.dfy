// <vc-preamble>
/*
 * Dafny specification for numpy.real_if_close functionality.
 * If input is complex with all imaginary parts close to zero, return real parts.
 * Otherwise, return the original complex vector.
 * "Close to zero" is defined as tol * (machine epsilon of the type).
 */

// Complex number datatype with real and imaginary parts
datatype Complex = Complex(re: real, im: real)

// Machine epsilon constant for floating point precision
const MACHINE_EPSILON: real := 2.2204460492503131 / 10000000000000000.0

// Helper predicate to check if a complex number's imaginary part is close to zero
predicate IsCloseToZero(c: Complex, tol: real)
  requires tol > 0.0
{
  var absIm := if c.im >= 0.0 then c.im else -c.im;
  absIm <= tol * MACHINE_EPSILON
}

// Helper predicate to check if all imaginary parts in a complex vector are close to zero
predicate AllImaginaryPartsCloseToZero(arr: seq<Complex>, tol: real)
  requires tol > 0.0
{
  forall i :: 0 <= i < |arr| ==> IsCloseToZero(arr[i], tol)
}

// Main method implementing real_if_close behavior
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate that all imaginary parts are exactly zero */
predicate AllImagZero(arr: seq<Complex>)
{
  forall i :: 0 <= i < |arr| ==> arr[i].im == 0.0
}

/* helper modified by LLM (iteration 3): helper to construct a complex number with zero imaginary part */
function MakeZeroImag(c: Complex): Complex
  ensures MakeZeroImag(c).re == c.re
  ensures MakeZeroImag(c).im == 0.0
{
  Complex(c.re, 0.0)
}
// </vc-helpers>

// <vc-spec>
method RealIfClose(arr: seq<Complex>, tol: real := 100.0) returns (result: seq<Complex>)
  requires tol > 0.0
  // Result vector has same length as input
  ensures |result| == |arr|
  // Real parts are always preserved
  ensures forall i :: 0 <= i < |arr| ==> result[i].re == arr[i].re
  // If all imaginary parts are close to zero, return real parts only (imaginary parts become 0)
  ensures AllImaginaryPartsCloseToZero(arr, tol) ==> 
    forall i :: 0 <= i < |arr| ==> result[i] == Complex(arr[i].re, 0.0)
  // Otherwise, preserve original complex numbers
  ensures !AllImaginaryPartsCloseToZero(arr, tol) ==> 
    forall i :: 0 <= i < |arr| ==> result[i] == arr[i]
  // Mathematical property: if input is already real, output equals input
  ensures (forall i :: 0 <= i < |arr| ==> arr[i].im == 0.0) ==> 
    forall i :: 0 <= i < |arr| ==> result[i] == arr[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): construct result sequence via loop, branching on closeness */
{
  var allClose := AllImaginaryPartsCloseToZero(arr, tol);
  var res: seq<Complex> := [];
  var i: int := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j].re == arr[j].re
    invariant forall j :: 0 <= j < i ==> (allClose ==> res[j] == Complex(arr[j].re, 0.0)) && (!allClose ==> res[j] == arr[j])
    decreases |arr| - i
  {
    var v := if allClose then MakeZeroImag(arr[i]) else arr[i];
    res := res + [v];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
