// <vc-preamble>
// Complex number datatype with real and imaginary components
datatype Complex = Complex(re: real, im: real)
// </vc-preamble>

// <vc-helpers>

predicate IsReal(c: Complex) { c.im == 0.0 }

/* helper modified by LLM (iteration 3): Removed lemma that was unnecessary and caused issues */

// </vc-helpers>

// <vc-spec>
method isreal(x: seq<Complex>) returns (result: seq<bool>)
  // Output array has same length as input array
  ensures |result| == |x|
  
  // Core property: element is real iff its imaginary part is zero
  ensures forall i :: 0 <= i < |x| ==> result[i] == (x[i].im == 0.0)
  
  // Real number detection: elements with zero imaginary part return true
  ensures forall i :: 0 <= i < |x| ==> (x[i].im == 0.0 ==> result[i])
  
  // Complex number detection: elements with non-zero imaginary part return false  
  ensures forall i :: 0 <= i < |x| ==> (x[i].im != 0.0 ==> !result[i])
  
  // Consistency: true result implies zero imaginary part
  ensures forall i :: 0 <= i < |x| ==> (result[i] ==> x[i].im == 0.0)
  
  // Consistency: false result implies non-zero imaginary part
  ensures forall i :: 0 <= i < |x| ==> (!result[i] ==> x[i].im != 0.0)
  
  // Bidirectional equivalence: real iff imaginary part is zero
  ensures forall i :: 0 <= i < |x| ==> (result[i] <==> x[i].im == 0.0)
  
  // Element-wise independence: each element tested independently
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && i != j ==> 
    (result[i] == (x[i].im == 0.0) && result[j] == (x[j].im == 0.0))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed sequence creation and element assignment */
  result := [];
  var index := 0;
  while index < |x|
    invariant 0 <= index <= |x|
    invariant |result| == index
    invariant forall j :: 0 <= j < index ==> result[j] == (x[j].im == 0.0)
  {
    result := result + [x[index].im == 0.0];
    index := index + 1;
  }
}
// </vc-code>
