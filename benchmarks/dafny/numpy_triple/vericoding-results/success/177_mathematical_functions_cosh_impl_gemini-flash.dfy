// <vc-preamble>
// Mathematical helper functions for specification
function Exp(x: real): real
  requires true
{
  1.0 // Placeholder for exponential function
}

function Abs(x: real): real
{
  if x >= 0.0 then x else -x
}

// Hyperbolic cosine element-wise computation
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): The helper function definition remains correct. */
function cosh_calc(val: real): real {
  (Exp(val) + Exp(-val)) / 2.0
}
// </vc-helpers>

// <vc-spec>
method numpy_cosh(x: seq<real>) returns (result: seq<real>)
  // No preconditions - hyperbolic cosine is defined for all real numbers
  requires true
  
  ensures |result| == |x|
  
  // Core mathematical definition: cosh(x) = (e^x + e^(-x))/2
  ensures forall i :: 0 <= i < |x| ==>
    result[i] == (Exp(x[i]) + Exp(-x[i])) / 2.0
  
  // Minimum value property: cosh(x) >= 1 for all x
  ensures forall i :: 0 <= i < |x| ==>
    result[i] >= 1.0
  
  // Even function property: cosh(-x) = cosh(x)
  ensures forall i :: 0 <= i < |x| ==>
    (Exp(-x[i]) + Exp(x[i])) / 2.0 == (Exp(x[i]) + Exp(-x[i])) / 2.0
  
  // Monotonicity on non-negative reals: x >= 0 implies cosh(x) >= cosh(0) = 1
  ensures forall i :: 0 <= i < |x| && x[i] >= 0.0 ==>
    result[i] >= 1.0
  
  // Symmetry property: cosh(x) = cosh(|x|)
  ensures forall i :: 0 <= i < |x| ==>
    result[i] == (Exp(Abs(x[i])) + Exp(-Abs(x[i]))) / 2.0
  
  // Identity property: cosh(0) = 1
  ensures forall i :: 0 <= i < |x| && x[i] == 0.0 ==>
    result[i] == 1.0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Corrected the loop bounds and ensured postconditions are met. */
{
  var temp_result_arr := new real[|x|];
  for i := 0 to |x|
    invariant 0 <= i <= |x|
    invariant forall k :: 0 <= k < i ==> temp_result_arr[k] == cosh_calc(x[k])
  {
    if i < |x| {
      temp_result_arr[i] := cosh_calc(x[i]);
    }
  }
  result := temp_result_arr[..];
}
// </vc-code>
