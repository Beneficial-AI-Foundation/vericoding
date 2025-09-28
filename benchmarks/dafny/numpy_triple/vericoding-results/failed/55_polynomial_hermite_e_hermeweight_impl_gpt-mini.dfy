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
/* helper modified by LLM (iteration 5): bridge to ExpPositive axiom */
lemma ExpPositive_helper(z: real)
  ensures RealExp(z) > 0.0
{
  ExpPositive(z);
}

/* helper modified by LLM (iteration 5): bridge to ExpSymmetryProperty axiom */
lemma ExpSymmetry_helper(a: real, b: real)
  ensures RealAbs(a) == RealAbs(b) ==> RealExp(-a*a/2.0) == RealExp(-b*b/2.0)
{
  ExpSymmetryProperty(a, b);
}

/* helper modified by LLM (iteration 5): prove positivity for each element */
lemma HermeWeight_elem_positive(x: seq<real>, i: int)
  requires 0 <= i < |x|
  ensures RealExp(-x[i]*x[i]/2.0) > 0.0
{
  ExpPositive(-x[i]*x[i]/2.0);
}

/* helper modified by LLM (iteration 5): prove symmetry implication for elements */
lemma HermeWeight_symmetry_elem(x: seq<real>, i: int, j: int)
  requires 0 <= i < |x|
  requires 0 <= j < |x|
  ensures RealAbs(x[i]) == RealAbs(x[j]) ==> RealExp(-x[i]*x[i]/2.0) == RealExp(-x[j]*x[j]/2.0)
{
  ExpSymmetryProperty(x[i], x[j]);
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
  /* code modified by LLM (iteration 5): build result sequence and discharge element-wise facts */
  var a := new real[|x|];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall k :: 0 <= k < i ==> a[k] == RealExp(-x[k] * x[k] / 2.0)
  {
    a[i] := RealExp(-x[i] * x[i] / 2.0);
    i := i + 1;
  }
  // Prove element-wise positivity using helper
  var j := 0;
  while j < |x|
    invariant 0 <= j <= |x|
  {
    HermeWeight_elem_positive(x, j);
    j := j + 1;
  }
  // Prove symmetry implication for all pairs (used to help the verifier):
  var p := 0;
  while p < |x|
    invariant 0 <= p <= |x|
  {
    var q := 0;
    while q < |x|
      invariant 0 <= q <= |x|
    {
      HermeWeight_symmetry_elem(x, p, q);
      q := q + 1;
    }
    p := p + 1;
  }
  result := a[..];
}

// </vc-code>
