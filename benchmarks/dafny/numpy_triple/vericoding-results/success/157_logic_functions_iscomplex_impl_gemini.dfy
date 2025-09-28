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
/* helper modified by LLM (iteration 3): fixed ensures clauses syntax */
function Map<T, U>(s: seq<T>, f: T -> U): seq<U>
  ensures |Map(s, f)| == |s|
  ensures forall i :: 0 <= i < |s| ==> Map(s, f)[i] == f(s[i])
{
  if |s| == 0 then []
  else [f(s[0])] + Map(s[1..], f)
}
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
  /* code modified by LLM (iteration 3): explicitly typed lambda parameter */
  result := Map(x, (c: Complex) => c.im != 0.0);
}
// </vc-code>
