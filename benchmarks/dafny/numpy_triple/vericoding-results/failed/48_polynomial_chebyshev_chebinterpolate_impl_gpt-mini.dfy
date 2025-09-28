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
{
  /* code modified by LLM (iteration 5): initialize coefficients, prove ChebPoint properties, and handle constant function interpolation */
  // Initialize an array of deg+1 reals to 0.0
  var a := new real[deg + 1];
  var i := 0;
  while i < deg + 1
    invariant 0 <= i <= deg + 1
    invariant forall t :: 0 <= t < i ==> a[t] == 0.0
    modifies a
  {
    a[i] := 0.0;
    i := i + 1;
  }

  // Set the constant term to func(0.0)
  a[0] := func(0.0);
  coeffs := a[..];

  // Prove ChebPoint range for all k (ensures property 3)
  var k := 0;
  while k <= deg
    invariant 0 <= k <= deg + 1
  {
    ChebPointRange(k, deg);
    k := k + 1;
  }

  // Prove ChebPoint ordering for all i < j (ensures property 4)
  var ii := 0;
  while ii <= deg
    invariant 0 <= ii <= deg + 1
  {
    var jj := ii + 1;
    while jj <= deg
      invariant ii + 1 <= jj <= deg + 1
    {
      ChebPointOrder(ii, jj, deg);
      jj := jj + 1;
    }
    ii := ii + 1;
  }

  // If func is constant, prove interpolation property (ensures property 2) and coefficient property (ensures property 1)
  if IsConstantFunction(func) {
    // coeffs[0] equals func(0.0)
    assert coeffs[0] == func(0.0);

    // All higher coefficients are 0.0
    assert forall i2 :: 1 <= i2 < |coeffs| ==> coeffs[i2] == 0.0;

    // Now invoke lemma to prove interpolation at Chebyshev points for constant functions
    ConstFunctionInterp(deg, func, coeffs);
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
/* helper modified by LLM (iteration 5): ChebPointRange */
lemma ChebPointRange(k: int, deg: nat)
  requires 0 <= k <= deg
  ensures -1.0 <= ChebPoint(k, deg) <= 1.0
{
  if deg == 0 {
    assert ChebPoint(k, deg) == 0.0;
    assert -1.0 <= 0.0 <= 1.0;
  } else {
    assert ChebPoint(k, deg) == 1.0 - 2.0 * (k as real) / (deg as real);
    // 0 <= k/deg <= 1
    assert 0.0 <= (k as real) / (deg as real);
    assert (k as real) / (deg as real) <= 1.0;
    assert -1.0 <= 1.0 - 2.0 * (k as real) / (deg as real) <= 1.0;
  }
}

/* helper modified by LLM (iteration 5): ChebPointOrder */
lemma ChebPointOrder(i: int, j: int, deg: nat)
  requires 0 <= i < j <= deg
  ensures ChebPoint(j, deg) < ChebPoint(i, deg)
{
  // deg cannot be 0 because 0 <= i < j <= deg
  assert deg > 0;
  assert ChebPoint(i, deg) == 1.0 - 2.0 * (i as real) / (deg as real);
  assert ChebPoint(j, deg) == 1.0 - 2.0 * (j as real) / (deg as real);
  assert (i as real) / (deg as real) < (j as real) / (deg as real);
  assert 1.0 - 2.0 * (j as real) / (deg as real) < 1.0 - 2.0 * (i as real) / (deg as real);
}

/* helper modified by LLM (iteration 5): ConstFunctionInterp */
lemma ConstFunctionInterp(deg: nat, func: RealFunction, coeffs: seq<real>)
  requires |coeffs| == deg + 1
  requires IsConstantFunction(func)
  requires coeffs[0] == func(0.0)
  requires forall i :: 1 <= i < |coeffs| ==> coeffs[i] == 0.0
  ensures forall k :: 0 <= k <= deg ==> -0.0000000001 <= EvaluateChebPoly(coeffs, ChebPoint(k, deg)) - func(ChebPoint(k, deg)) <= 0.0000000001
{
  var k := 0;
  while k <= deg
    invariant 0 <= k <= deg + 1
  {
    var x := ChebPoint(k, deg);
    var poly := EvaluateChebPoly(coeffs, x);
    // By the requires, coeffs[0] == func(0.0) and coeffs[i>=1]==0
    if |coeffs| > 1 {
      assert coeffs[1] == 0.0;
      assert poly == coeffs[0] + coeffs[1] * x;
      assert poly == coeffs[0];
    } else {
      assert poly == coeffs[0];
    }
    // func is constant
    assert func(x) == func(0.0);
    assert poly - func(x) == coeffs[0] - func(0.0);
    assert coeffs[0] - func(0.0) == 0.0;
    assert -0.0000000001 <= poly - func(x) <= 0.0000000001;
    k := k + 1;
  }
}

// </vc-code>
