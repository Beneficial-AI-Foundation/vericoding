// <vc-preamble>
/*
 * Dafny specification for numpy.iscomplex function.
 * Returns a bool array where True if input element has non-zero imaginary part.
 * Tests whether the input has a non-zero imaginary part, not the input type.
 */

// Complex number datatype with real and imaginary components
datatype Complex = Complex(re: real, im: real)

// Method specification for iscomplex function
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method iscomplex(x: seq<Complex>) returns (result: seq<bool>)
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> (result[i] <==> (x[i].im != 0.0))
  ensures forall i :: 0 <= i < |x| ==> (x[i].im == 0.0 ==> result[i] == false)
  ensures forall i :: 0 <= i < |x| ==> (x[i].im != 0.0 ==> result[i] == true)
  ensures forall i :: 0 <= i < |x| ==> (result[i] == true ==> x[i].im != 0.0)
  ensures forall i :: 0 <= i < |x| ==> (result[i] == false ==> x[i].im == 0.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
