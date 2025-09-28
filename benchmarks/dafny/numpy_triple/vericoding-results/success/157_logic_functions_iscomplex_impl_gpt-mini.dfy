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
/* helper modified by LLM (iteration 2): relate inequality and negated equality for reals */
lemma ImNonzeroEquivalence(r: real)
  ensures (r != 0.0) <==> !(r == 0.0)
{
  if r == 0.0 {
    assert !(r != 0.0);
  } else {
    assert r != 0.0;
  }
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
  /* code modified by LLM (iteration 2): build result as seq by concatenation */
  var n := |x|;
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> (result[j] <==> (x[j].im != 0.0))
  {
    result := result + [x[i].im != 0.0];
    i := i + 1;
  }
}

// </vc-code>
