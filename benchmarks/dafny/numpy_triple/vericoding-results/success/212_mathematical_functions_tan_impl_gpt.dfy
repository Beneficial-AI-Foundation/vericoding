// <vc-preamble>
/*
 * Computes tangent element-wise for vectors. Equivalent to sin(x)/cos(x) element-wise.
 * The function is undefined when cos(x) = 0 (i.e., x = π/2 + kπ for integer k).
 */

// Uninterpreted trigonometric functions
function sin(x: real): real
{
  0.0  // Dummy implementation for compilation
}

function cos(x: real): real
{
  1.0  // Dummy implementation for compilation
}

function tan(x: real): real
{
  0.0  // Dummy implementation for compilation
}

// Axiom relating tan to sin and cos
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): instantiate quantified precondition to show cos(x[i]) != 0 */
lemma CosNonZeroAtIndex(x: seq<real>, i: int)
  requires 0 <= i < |x|
  requires forall j :: 0 <= j < |x| ==> cos(x[j]) != 0.0
  ensures cos(x[i]) != 0.0
{
  assert 0 <= i < |x|;
  assert cos(x[i]) != 0.0;
}
// </vc-helpers>

// <vc-spec>
lemma {:axiom} tan_definition(x: real)
  requires cos(x) != 0.0
  ensures tan(x) == sin(x) / cos(x)

// Element-wise tangent computation method
method TanElementwise(x: seq<real>) returns (result: seq<real>)
  // Precondition: cosine of each element must be non-zero
  requires forall i :: 0 <= i < |x| ==> cos(x[i]) != 0.0
  // Postcondition: result has same length as input
  ensures |result| == |x|
  // Postcondition: each element is the tangent of corresponding input element
  ensures forall i :: 0 <= i < |x| ==> result[i] == tan(x[i])
  // Postcondition: each element equals sin(x)/cos(x) for corresponding input
  ensures forall i :: 0 <= i < |x| ==> result[i] == sin(x[i]) / cos(x[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): use correct array construction and explicit postcondition proofs */
  var n := |x|;
  var arr := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> cos(x[k]) != 0.0
    invariant forall k :: 0 <= k < i ==> arr[k] == tan(x[k])
    decreases n - i
  {
    CosNonZeroAtIndex(x, i);
    arr[i] := tan(x[i]);
    i := i + 1;
  }
  assert i == n;
  result := arr[..];
  assert |result| == n;
  // Each element equals tan(x[i])
  assert forall j :: 0 <= j < n ==> arr[j] == tan(x[j]);
  assert forall j :: 0 <= j < n ==> result[j] == arr[j];
  assert forall j :: 0 <= j < n ==> result[j] == tan(x[j]);
  // And equals sin(x)/cos(x)
  forall j | 0 <= j < n
    ensures tan(x[j]) == sin(x[j]) / cos(x[j])
  {
    CosNonZeroAtIndex(x, j);
    tan_definition(x[j]);
  }
  assert forall j :: 0 <= j < n ==> result[j] == sin(x[j]) / cos(x[j]);
}
// </vc-code>
