// <vc-preamble>
// Function type for real-valued functions of a single real variable
type RealFunction = real -> real

// Helper function to compute the k-th Chebyshev point of the first kind for degree deg
function ChebPoint(k: int, deg: nat): real
  requires 0 <= k <= deg as int
{
  // x_k = cos(π * k / deg) 
  // Using mathematical representation - actual computation would use trigonometric functions
  if deg == 0 then 0.0 else 1.0 - 2.0 * (k as real) / (deg as real)  // Approximation for specification
}

// Helper function to evaluate a Chebyshev polynomial with given coefficients at a point
function EvaluateChebPoly(coeffs: seq<real>, x: real): real
  requires |coeffs| > 0
{
  // This would compute the Chebyshev polynomial evaluation
  // For specification purposes, we use a simplified form
  coeffs[0] + if |coeffs| > 1 then coeffs[1] * x else 0.0
}

// Check if a function is constant
ghost predicate IsConstantFunction(f: RealFunction)
{
  forall x1, x2 :: f(x1) == f(x2)
}

// Main interpolation method
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ChebInterpolate(deg: nat, func: RealFunction) returns (coeffs: seq<real>)
  ensures |coeffs| == deg + 1
  // Property 1: For constant functions, only the first coefficient is non-zero
  ensures IsConstantFunction(func) ==> 
    (coeffs[0] == func(0.0) && forall i :: 1 <= i < |coeffs| ==> coeffs[i] == 0.0)
  // Property 2: The interpolation is exact at all Chebyshev points
  ensures forall k :: 0 <= k <= deg ==> 
    var cheb_point := ChebPoint(k, deg);
    var poly_value := EvaluateChebPoly(coeffs, cheb_point);
    var func_value := func(cheb_point);
    -0.0000000001 <= poly_value - func_value <= 0.0000000001
  // Property 3: All Chebyshev points are in the interval [-1, 1]
  ensures forall k :: 0 <= k <= deg ==> 
    var cheb_point := ChebPoint(k, deg);
    -1.0 <= cheb_point <= 1.0
  // Property 4: Chebyshev points are ordered (descending for first kind)
  ensures forall i, j :: 0 <= i < j <= deg ==> 
    ChebPoint(j, deg) < ChebPoint(i, deg)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed division by zero and constant function handling */
  // Initialize coefficients sequence
  coeffs := [];
  var i := 0;
  
  // Build coefficient sequence of length deg + 1
  while i <= deg
    invariant 0 <= i <= deg + 1
    invariant |coeffs| == i
  {
    if i == 0 {
      // First coefficient is the function value at x=0 (or first Chebyshev point)
      coeffs := coeffs + [func(0.0)];
    } else {
      // For constant functions, all other coefficients should be 0
      // For non-constant functions, we'd compute proper Chebyshev coefficients
      // Check if function appears constant by comparing values
      var val0 := func(0.0);
      var cheb_point := ChebPoint(i, deg);
      var func_val := func(cheb_point);
      
      // If values are equal (within tolerance), coefficient is 0 (constant function case)
      if -0.0000000001 <= func_val - val0 <= 0.0000000001 {
        coeffs := coeffs + [0.0];
      } else if cheb_point != 0.0 {
        // Non-constant function: compute coefficient
        // For our simplified linear model
        var coeff_val := (func_val - coeffs[0]) / cheb_point;
        coeffs := coeffs + [coeff_val];
      } else {
        // cheb_point is 0, use 0 coefficient
        coeffs := coeffs + [0.0];
      }
    }
    i := i + 1;
  }
  
  // Fine-tune coefficients for better interpolation accuracy
  // Ensure we satisfy the interpolation condition at Chebyshev points
  if deg > 0 && |coeffs| > 1 {
    var x1 := ChebPoint(1, deg);
    if x1 != 0.0 {
      var target_val := func(x1);
      var current_val := EvaluateChebPoly(coeffs, x1);
      // Only adjust if there's significant error
      if !((-0.0000000001 <= current_val - target_val <= 0.0000000001)) {
        var adjust := (target_val - coeffs[0]) / x1;
        coeffs := coeffs[1 := adjust];
      }
    }
  }
}
// </vc-code>
