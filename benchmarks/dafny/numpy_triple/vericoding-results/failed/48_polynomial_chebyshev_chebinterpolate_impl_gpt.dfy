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
/* helper modified by LLM (iteration 5): construct a sequence of zeros of given length */
function Zeros(n: nat): seq<real>
  ensures |Zeros(n)| == n
  ensures forall i :: 0 <= i < n ==> Zeros(n)[i] == 0.0
  decreases n
{
  if n == 0 then [] else [0.0] + Zeros(n - 1)
}

/* helper modified by LLM (iteration 5): prove all Chebyshev points lie in [-1,1] for our linearized ChebPoint */
lemma ChebPointsInRange(deg: nat)
  ensures forall k :: 0 <= k <= deg ==> -1.0 <= ChebPoint(k, deg) <= 1.0
{
  if deg == 0 {
    forall k | 0 <= k <= deg {
      assert k == 0;
      assert ChebPoint(k, deg) == 0.0;
      assert -1.0 <= 0.0 <= 1.0;
    }
  } else {
    assert (deg as real) > 0.0;
    forall k | 0 <= k <= deg {
      var r := (k as real) / (deg as real);
      assert 0.0 <= r;
      assert r <= 1.0;
      assert -1.0 <= 1.0 - 2.0 * r;
      assert 1.0 - 2.0 * r <= 1.0;
    }
  }
}

/* helper modified by LLM (iteration 5): show monotonicity (strictly decreasing) of Chebyshev points for deg>0 */
lemma ChebPointsStrictlyDecreasing(deg: nat)
  ensures forall i, j :: 0 <= i < j <= deg ==> ChebPoint(j, deg) < ChebPoint(i, deg)
{
  if deg == 0 {
  } else {
    assert (deg as real) > 0.0;
    forall i, j | 0 <= i < j <= deg {
      var ri := (i as real) / (deg as real);
      var rj := (j as real) / (deg as real);
      assert (i as real) < (j as real);
      assert ri < rj; // division by positive preserves inequality
      assert 1.0 - 2.0 * rj < 1.0 - 2.0 * ri;
    }
  }
}

/* helper modified by LLM (iteration 5): evaluation depends only on first two coefficients by definition */
lemma EvalDependsOnFirstTwo(coeffs: seq<real>, x: real)
  requires |coeffs| >= 2
  ensures EvaluateChebPoly(coeffs, x) == EvaluateChebPoly([coeffs[0], coeffs[1]], x)
{
  assert EvaluateChebPoly(coeffs, x) == coeffs[0] + coeffs[1] * x;
  assert EvaluateChebPoly([coeffs[0], coeffs[1]], x) == coeffs[0] + coeffs[1] * x;
}

/* helper modified by LLM (iteration 5): for deg=1, linear coefficients match function at endpoints */
lemma LinearMatchesEndpoints(func: RealFunction)
  ensures var a := (func(1.0) + func(-1.0)) / 2.0;
          var b := (func(1.0) - func(-1.0)) / 2.0;
          EvaluateChebPoly([a, b], 1.0) == func(1.0) &&
          EvaluateChebPoly([a, b], -1.0) == func(-1.0)
{
  var a := (func(1.0) + func(-1.0)) / 2.0;
  var b := (func(1.0) - func(-1.0)) / 2.0;
  assert EvaluateChebPoly([a, b], 1.0) == a + b * 1.0;
  assert EvaluateChebPoly([a, b], -1.0) == a - b;
  assert a + b == func(1.0);
  assert a - b == func(-1.0);
}

/* helper modified by LLM (iteration 5): establish exactness at Chebyshev points when deg <= 1 */
lemma InterpExactAtChebPointsDegLE1(deg: nat, func: RealFunction, coeffs: seq<real>)
  requires deg <= 1
  requires if deg == 0 then coeffs == [func(0.0)] else true
  requires if deg == 1 then coeffs == [(func(1.0) + func(-1.0)) / 2.0, (func(1.0) - func(-1.0)) / 2.0] else true
  ensures forall k :: 0 <= k <= deg ==> 
    var cheb_point := ChebPoint(k, deg);
    var poly_value := EvaluateChebPoly(coeffs, cheb_point);
    var func_value := func(cheb_point);
    -0.0000000001 <= poly_value - func_value <= 0.0000000001
{
  if deg == 0 {
    forall k | 0 <= k <= deg {
      assert k == 0;
      assert ChebPoint(k, deg) == 0.0;
      assert EvaluateChebPoly(coeffs, 0.0) == coeffs[0];
      assert coeffs[0] == func(0.0);
      assert -0.0000000001 <= 0.0 <= 0.0000000001;
    }
  } else {
    // deg == 1
    LinearMatchesEndpoints(func);
    forall k | 0 <= k <= deg {
      if k == 0 {
        assert ChebPoint(0, 1) == 1.0;
        assert EvaluateChebPoly(coeffs, 1.0) == func(1.0);
        assert -0.0000000001 <= 0.0 <= 0.0000000001;
      } else {
        assert k == 1;
        assert ChebPoint(1, 1) == -1.0;
        assert EvaluateChebPoly(coeffs, -1.0) == func(-1.0);
        assert -0.0000000001 <= 0.0 <= 0.0000000001;
      }
    }
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
  /* code modified by LLM (iteration 5): construct linear/constant coefficients and discharge range/order and small-degree exactness */
  if deg == 0 {
    coeffs := [func(0.0)];
  } else {
    var f1 := func(1.0);
    var fm1 := func(-1.0);
    var a := (f1 + fm1) / 2.0;
    var b := (f1 - fm1) / 2.0;
    if deg == 1 {
      coeffs := [a, b];
    } else {
      var z := Zeros((deg - 1) as nat);
      coeffs := [a, b] + z;
    }
  }
  // Establish geometric properties of Chebyshev nodes
  ChebPointsInRange(deg);
  ChebPointsStrictlyDecreasing(deg);

  // For small degrees, prove exactness at Chebyshev points
  if deg <= 1 {
    if deg == 0 {
      InterpExactAtChebPointsDegLE1(deg, func, coeffs);
    } else {
      InterpExactAtChebPointsDegLE1(deg, func, coeffs);
    }
  }
}
// </vc-code>
