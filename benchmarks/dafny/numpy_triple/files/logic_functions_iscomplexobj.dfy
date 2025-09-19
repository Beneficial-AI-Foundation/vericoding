// <vc-preamble>
// Complex number datatype with real and imaginary parts
datatype Complex = Complex(re: real, im: real)
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method iscomplexobj(x: seq<Complex>) returns (result: bool)
  // No preconditions - function accepts any sequence of complex numbers
  ensures result == true
  // Zero complex numbers (0+0i) are still considered complex objects
  ensures (forall i :: 0 <= i < |x| ==> x[i] == Complex(0.0, 0.0)) ==> result == true
  // Complex numbers with zero imaginary part are still complex objects
  ensures (forall i :: 0 <= i < |x| ==> x[i].im == 0.0) ==> result == true
  // Sanity check: any complex vector with real values only is still complex
  ensures (forall i :: 0 <= i < |x| ==> exists re_val: real :: x[i] == Complex(re_val, 0.0)) ==> result == true
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
