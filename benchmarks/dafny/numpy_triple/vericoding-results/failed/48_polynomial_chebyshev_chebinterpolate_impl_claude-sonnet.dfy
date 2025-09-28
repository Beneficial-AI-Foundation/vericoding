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
predicate IsConstantFunctionHelper(f: RealFunction, x1: real, x2: real): bool
{
  f(x1) == f(x2)
}

predicate ValidChebSequence(coeffs: seq<real>, deg: nat, func: RealFunction)
{
  |coeffs| == deg + 1 &&
  (forall k :: 0 <= k <= deg ==> 
    var cheb_point := ChebPoint(k, deg);
    var poly_value := EvaluateChebPoly(coeffs, cheb_point);
    var func_value := func(cheb_point);
    -0.0000000001 <= poly_value - func_value <= 0.0000000001)
}

function ComputeChebCoeff(k: int, deg: nat, func: RealFunction): real
  requires 0 <= k <= deg
{
  func(ChebPoint(k, deg))
}

lemma ChebPointProperties(deg: nat)
  ensures forall k :: 0 <= k <= deg ==> -1.0 <= ChebPoint(k, deg) <= 1.0
  ensures forall i, j :: 0 <= i < j <= deg ==> ChebPoint(j, deg) < ChebPoint(i, deg)
{
  forall k | 0 <= k <= deg
    ensures -1.0 <= ChebPoint(k, deg) <= 1.0
  {
    if deg == 0 {
      assert ChebPoint(k, deg) == 0.0;
    } else {
      var point := 1.0 - 2.0 * (k as real) / (deg as real);
      assert 0.0 <= (k as real) / (deg as real) <= 1.0;
      assert -1.0 <= point <= 1.0;
    }
  }
  
  forall i, j | 0 <= i < j <= deg
    ensures ChebPoint(j, deg) < ChebPoint(i, deg)
  {
    if deg > 0 {
      var point_i := 1.0 - 2.0 * (i as real) / (deg as real);
      var point_j := 1.0 - 2.0 * (j as real) / (deg as real);
      assert (i as real) < (j as real);
      assert point_j < point_i;
    }
  }
}

lemma ConstantFunctionLemma(func: RealFunction, deg: nat)
  requires IsConstantFunction(func)
  ensures forall k :: 0 <= k <= deg ==> func(ChebPoint(k, deg)) == func(0.0)
{
  forall k | 0 <= k <= deg
    ensures func(ChebPoint(k, deg)) == func(0.0)
  {
    assert func(ChebPoint(k, deg)) == func(0.0);
  }
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
  /* code modified by LLM (iteration 5): simplified implementation without checking IsConstantFunction in compiled code */
  ChebPointProperties(deg);
  
  coeffs := [];
  var i := 0;
  while i <= deg
    invariant 0 <= i <= deg + 1
    invariant |coeffs| == i
    invariant forall j :: 0 <= j < i ==> coeffs[j] == ComputeChebCoeff(j, deg, func)
  {
    var coeff := ComputeChebCoeff(i, deg, func);
    coeffs := coeffs + [coeff];
    i := i + 1;
  }
  
  // Prove interpolation property
  forall k | 0 <= k <= deg
    ensures var cheb_point := ChebPoint(k, deg);
            var poly_value := EvaluateChebPoly(coeffs, cheb_point);
            var func_value := func(cheb_point);
            -0.0000000001 <= poly_value - func_value <= 0.0000000001
  {
    var cheb_point := ChebPoint(k, deg);
    var poly_value := EvaluateChebPoly(coeffs, cheb_point);
    var func_value := func(cheb_point);
    
    assert coeffs[0] == ComputeChebCoeff(0, deg, func);
    if |coeffs| > 1 {
      assert coeffs[1] == ComputeChebCoeff(1, deg, func);
    }
    
    if k == 0 {
      assert poly_value == coeffs[0];
      assert func_value == func(cheb_point);
      assert coeffs[0] == func(cheb_point);
    }
  }
}
// </vc-code>
