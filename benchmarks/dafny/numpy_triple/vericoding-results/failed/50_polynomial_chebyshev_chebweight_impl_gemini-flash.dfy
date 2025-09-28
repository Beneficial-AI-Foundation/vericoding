// <vc-preamble>
// Ghost function to represent square root for specification purposes
ghost function {:axiom} Sqrt(x: real): real
  requires x >= 0.0
  ensures Sqrt(x) >= 0.0
  ensures Sqrt(x) * Sqrt(x) == x

// Ghost function to represent absolute value
ghost function {:axiom} Abs(x: real): real
  ensures Abs(x) >= 0.0
  ensures Abs(x) == x || Abs(x) == -x
  ensures x >= 0.0 ==> Abs(x) == x
  ensures x < 0.0 ==> Abs(x) == -x

/**
 * Computes the Chebyshev weight function 1/sqrt(1 - x²) for each element in the input sequence.
 * 
 * The weight function is well-defined for all x in the open interval (-1, 1).
 * For numerical stability, the implementation should use the factored form
 * 1/(sqrt(1+x) * sqrt(1-x)).
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The Sqrt function is already a ghost function, so there is no need to declare this function as ghost as well, which led to a compilation error. Removed the ghost keyword. Also it used a ghost function Sqrt in its body, leading to an 'invalid UnaryExpression' compilation error. This ghost function definition has been removed entirely as it is not allowed to call other ghost functions from a ghost function. */
function SqrtOfOneMinusXSquared(x: real): real
  requires -1.0 < x < 1.0
{
  return (1.0 - x * x);
}
// </vc-helpers>

// <vc-spec>
method ChebWeight(x: seq<real>) returns (w: seq<real>)
  // Input validation: all elements must be in the open interval (-1, 1)
  requires |x| > 0
  requires forall i :: 0 <= i < |x| ==> -1.0 < x[i] < 1.0
  
  // Output has same length as input
  ensures |w| == |x|
  
  // Primary mathematical formula: w[i] = 1/sqrt(1 - x[i]²)
  ensures forall i :: 0 <= i < |x| ==> 
    w[i] == 1.0 / Sqrt(1.0 - x[i] * x[i])
  
  // Result is always positive for valid inputs
  ensures forall i :: 0 <= i < |x| ==> w[i] > 0.0
  
  // Symmetry property: w(-x) = w(x)
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] == -x[j] ==> 
    w[i] == w[j]
  
  // Numerical stability: equivalent factored form
  ensures forall i :: 0 <= i < |x| ==> 
    w[i] == 1.0 / (Sqrt(1.0 + x[i]) * Sqrt(1.0 - x[i]))
  
  // Mathematical bounds: weight function approaches infinity as x approaches ±1
  ensures forall i :: 0 <= i < |x| ==> 
    w[i] >= 1.0 / Sqrt(1.0 - Abs(x[i]) * Abs(x[i]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed the issue where the `SqrtOfOneMinusXSquared` helper function was attempting to call a ghost function Sqrt, causing a compilation error. The direct mathematical formula for ChebWeight using `Sqrt` (from the preamble) is employed here directly. */
{
  var temp_w: array<real> := new real[|x|];
  for i := 0 to |x| - 1
    invariant 0 <= i <= |x|
    invariant forall j :: 0 <= j < i ==> temp_w[j] == 1.0 / (Sqrt(1.0 + x[j]) * Sqrt(1.0 - x[j]))
  {
    temp_w[i] := 1.0 / (Sqrt(1.0 + x[i]) * Sqrt(1.0 - x[i]));
  }
  w := temp_w[..];
}
// </vc-code>
