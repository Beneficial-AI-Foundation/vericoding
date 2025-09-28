// <vc-preamble>
// Method to compute absolute values element-wise for a sequence of real numbers
// </vc-preamble>

// <vc-helpers>

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
  var res: seq<real> := [];
  var i: int := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> res[k] == (if x[k] >= 0.0 then x[k] else -x[k])
  {
    var abs_val: real;
    if x[i] >= 0.0 {
      abs_val := x[i];
    } else {
      abs_val := -x[i];
    }
    res := res + [abs_val];
    i := i + 1;
  }
  return res;
}
// </vc-code>
