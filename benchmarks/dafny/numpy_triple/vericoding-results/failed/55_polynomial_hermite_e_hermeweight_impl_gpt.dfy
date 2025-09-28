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
/* helper modified by LLM (iteration 5): positivity of RealExp via provided axiom */
lemma PosExpArg(a: real)
  ensures RealExp(a) > 0.0
{
  ExpPositive(a);
}

/* helper modified by LLM (iteration 5): symmetry of weights under equal absolute values via provided axiom */
lemma SymmetryExpFromAbs(x: real, y: real)
  ensures RealAbs(x) == RealAbs(y) ==> RealExp(-x*x/2.0) == RealExp(-y*y/2.0)
{
  ExpSymmetryProperty(x, y);
}
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
  /* code modified by LLM (iteration 5): construct weights with loop invariants ensuring element formula and positivity; avoid brittle global assertions */
  var n := |x|;
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == RealExp(-x[k]*x[k]/2.0)
    invariant forall k :: 0 <= k < i ==> result[k] > 0.0
    decreases n - i
  {
    var w := RealExp(-x[i]*x[i]/2.0);
    // show positivity for the new element
    PosExpArg(-x[i]*x[i]/2.0);
    result := result + [w];
    i := i + 1;
  }
}
// </vc-code>
