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
/* helper modified by LLM (iteration 5): Added helper function for sequence comprehension */
function CreateConstantSequence(value: real, length: nat): seq<real>
  requires length >= 0
  ensures |CreateConstantSequence(value, length)| == length
  ensures forall i :: 0 <= i < length ==> CreateConstantSequence(value, length)[i] == value
{
  if length == 0 then [] else [value] + CreateConstantSequence(value, length - 1)
}
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
  /* code modified by LLM (iteration 5): Fixed sequence comprehension syntax by using helper function */
  if deg == 0 {
    coeffs := [func(0.0)];
  } else {
    if deg == 1 {
      var x0 := ChebPoint(0, 1);
      var x1 := ChebPoint(1, 1);
      var y0 := func(x0);
      var y1 := func(x1);
      var c1 := (y1 - y0) / (x1 - x0);
      var c0 := y0 - c1 * x0;
      coeffs := [c0, c1];
    } else {
      coeffs := [func(0.0)] + CreateConstantSequence(0.0, deg);
    }
  }
}
// </vc-code>
