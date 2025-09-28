// <vc-preamble>
// Mathematical functions needed for the specification
function RealExp(x: real): real
  // Exponential function - uninterpreted for specification purposes
{
  1.0  // Dummy implementation for compilation
}

function RealAbs(x: real): real
  // Absolute value function
  ensures RealAbs(x) >= 0.0
  ensures RealAbs(x) == x || RealAbs(x) == -x
  ensures x >= 0.0 ==> RealAbs(x) == x
  ensures x < 0.0 ==> RealAbs(x) == -x
{
  if x >= 0.0 then x else -x
}

// Properties of exponential function needed for specification
// </vc-preamble>

// <vc-helpers>
function AbsReal(x: real): real
  ensures AbsReal(x) >= 0.0
  ensures x >= 0.0 ==> AbsReal(x) == x
  ensures x < 0.0 ==> AbsReal(x) == -x
{
  if x >= 0.0 then x else -x
}

/* helper modified by LLM (iteration 5): Removed conflicting lemma and predicate, kept only necessary helper */
// </vc-helpers>

// <vc-spec>
lemma {:axiom} ExpPositive(x: real)
  ensures RealExp(x) > 0.0

lemma {:axiom} ExpSymmetryProperty(x: real, y: real)
  ensures RealAbs(x) == RealAbs(y) ==> RealExp(-x*x/2.0) == RealExp(-y*y/2.0)

/**
 * Computes the HermiteE weight function for a sequence of real values.
 * The weight function w(x) = exp(-x²/2) is applied element-wise.
 */
method hermeweight(x: seq<real>) returns (result: seq<real>)
  // No preconditions - weight function is defined for all real numbers
  
  // Result has same length as input
  ensures |result| == |x|
  
  // Each element follows the weight function formula: w(x) = exp(-x²/2)
  ensures forall i :: 0 <= i < |x| ==> result[i] == RealExp(-x[i] * x[i] / 2.0)
  
  // Weight function is always positive
  ensures forall i :: 0 <= i < |x| ==> result[i] > 0.0
  
  // Weight function is symmetric: w(x) = w(-x)
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| ==> 
    (result[i] == result[j] <==> RealAbs(x[i]) == RealAbs(x[j]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed array allocation type error - use seq constructor */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == RealExp(-x[j] * x[j] / 2.0)
    invariant forall j :: 0 <= j < i ==> result[j] > 0.0
    invariant forall k, l :: 0 <= k < i && 0 <= l < i ==> 
      (result[k] == result[l] <==> RealAbs(x[k]) == RealAbs(x[l]))
  {
    result := result + [RealExp(-x[i] * x[i] / 2.0)];
    i := i + 1;
  }
}
// </vc-code>
