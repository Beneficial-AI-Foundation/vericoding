// <vc-preamble>
// Method to compute absolute values element-wise for a sequence of real numbers
// </vc-preamble>

// <vc-helpers>
function absReal(r: real): real {
  if r >= 0.0 then r else -r
}
lemma absRealProperties(r: real)
  ensures absReal(r) >= 0.0
  ensures absReal(r) == if r >= 0.0 then r else -r
  ensures absReal(-r) == absReal(r)
  ensures absReal(absReal(r)) == absReal(r)
{
  // Properties follow from absReal definition
}

// </vc-helpers>

// <vc-spec>
method fabs(x: seq<real>) returns (result: seq<real>)
  // Ensures the result has the same length as input
  ensures |result| == |x|
  
  // Primary property: each element is the absolute value of the corresponding input element
  ensures forall i :: 0 <= i < |x| ==> result[i] == if x[i] >= 0.0 then x[i] else -x[i]
  
  // Non-negativity: all elements in result are non-negative
  ensures forall i :: 0 <= i < |result| ==> result[i] >= 0.0
  
  // Idempotence: absolute value of the result equals the result itself
  ensures forall i :: 0 <= i < |result| ==> 
    (if result[i] >= 0.0 then result[i] else -result[i]) == result[i]
  
  // Symmetry: abs(x) = abs(-x) for all elements
  ensures forall i :: 0 <= i < |x| ==> 
    result[i] == (if -x[i] >= 0.0 then -x[i] else -(-x[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed type error by using seq instead of array */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == absReal(x[j])
    invariant forall j :: 0 <= j < i ==> result[j] >= 0.0
  {
    result := result + [absReal(x[i])];
    i := i + 1;
  }
}
// </vc-code>
