// <vc-preamble>
// Method to compute absolute values element-wise for a sequence of real numbers
// </vc-preamble>

// <vc-helpers>
function absR(x: real): real { if x >= 0.0 then x else -x }
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
  var n := |x|;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == (if x[j] >= 0.0 then x[j] else -x[j])
  {
    a[i] := if x[i] >= 0.0 then x[i] else -x[i];
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
