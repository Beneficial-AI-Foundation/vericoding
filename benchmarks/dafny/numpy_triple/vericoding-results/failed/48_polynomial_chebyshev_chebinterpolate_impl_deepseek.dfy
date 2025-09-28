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
/* helpers modified by LLM (iteration 5): Fix while loop syntax and add proper invariants */
import opened Math

function ChebPointAccurate(k: int, deg: nat): real
  requires 0 <= k <= deg as int
{
  if deg == 0 then 0.0 else Cos(PI * (k as real) / (deg as real))
}

function EvaluateChebPolyAccurate(coeffs: seq<real>, x: real): (r: real)
  requires |coeffs| > 0
  decreases |coeffs|
{
  if |coeffs| == 1 then coeffs[0]
  else if |coeffs| == 2 then coeffs[0] + coeffs[1] * x
  else (
    var t0 := 1.0;
    var t1 := x;
    var result := coeffs[0] * t0 + coeffs[1] * t1;
    
    var i := 2;
    while i < |coeffs|
      invariant 2 <= i <= |coeffs|
      invariant result == EvaluateChebPolyAccurate(coeffs[0..i], x)
    {
      var t2 := 2.0 * x * t1 - t0;
      result := result + coeffs[i] * t2;
      t0 := t1;
      t1 := t2;
      i := i + 1;
    }
    result
  )
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
  /* code modified by LLM (iteration 5): Fixed while loop syntax and simplified calculation */
  var n := deg + 1;
  coeffs := new real[n];
  
  // Compute function values at Chebyshev points
  var fValues := new real[n];
  var k: int := 0;
  while k < n
    invariant 0 <= k <= n
    invariant forall i :: 0 <= i < k ==> fValues[i] == func(ChebPointAccurate(i, deg))
  {
    fValues[k] := func(ChebPointAccurate(k, deg));
    k := k + 1;
  }
  
  // Initialize coefficients using Chebyshev interpolation
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
  {
    var sum: real := 0.0;
    var j: int := 0;
    while j < n
      invariant 0 <= j <= n
      invariant sum == (if j > 0 then sum else 0.0) + (if j < n then fValues[j] * Cos(PI * (i as real) * (j as real) / (deg as real)) else 0.0)
    {
      var theta := PI * (j as real) / (deg as real);
      sum := sum + fValues[j] * Cos((i as real) * theta);
      j := j + 1;
    }
    
    coeffs[i] := (if i == 0 || i == deg then 0.5 * sum / (deg as real) else sum / (deg as real));
    i := i + 1;
  }
}
// </vc-code>
