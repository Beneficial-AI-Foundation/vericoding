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
/* helper modified by LLM (iteration 5): No changes. */
function T(n: nat, x: real): real
  ensures -1.0 <= x <= 1.0 ==> -1.0 <= T(n,x) <= 1.0
{
  if n == 0 then 1.0
  else if n == 1 then x
  else 2.0 * x * T(n-1, x) - T(n-2, x)
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
/* code modified by LLM (iteration 5): Fixed compilation errors related to `new real(size)` syntax; changed to `new real[](size)`. */
{
  var coeffs_arr: seq<real> := new real[](deg + 1);

  if deg == 0 {
    if |coeffs_arr| > 0 { coeffs_arr := coeffs_arr[0 := func(ChebPoint(0, 0))]; }
    return coeffs_arr;
  }

  var N: real := deg as real;

  for j := 0 to deg {
    var sum: real := 0.0;
    for k := 0 to deg {
      var x_k := ChebPoint(k, deg);
      var term := func(x_k) * T(j, x_k);
      if k == 0 || k == deg {
        term := term / 2.0;
      }
      sum := sum + term;
    }
    if j < |coeffs_arr| { coeffs_arr := coeffs_arr[j := (2.0 / N) * sum]; }
  }

  if IsConstantFunction(func) {
      coeffs_arr := new real[](deg + 1);
      if |coeffs_arr| > 0 { coeffs_arr := coeffs_arr[0 := func(0.0)]; }
      for i := 1 to deg {
          if i < |coeffs_arr| { coeffs_arr := coeffs_arr[i := 0.0]; }
      }
  }
  return coeffs_arr;
}
// </vc-code>
