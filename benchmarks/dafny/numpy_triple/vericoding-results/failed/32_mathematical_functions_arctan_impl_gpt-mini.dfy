// <vc-preamble>
// Vector type definition as sequence of real numbers (approximating floating point)
type Vector = seq<real>

// Mathematical constants (floating point approximations)
const PI_HALF: real := 1.5708
const PI_QUARTER: real := 0.7854
const EPSILON: real := 0.000001
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): absolute value helper */
function Abs(x: real): real
{
  if x >= 0.0 then x else -x
}

/* helper modified by LLM (iteration 5): scalar arctan approximation */
function atan_scalar(x: real): real
{
  if Abs(x) < 0.1 then x else PI_HALF * x / (1.0 + Abs(x))
}

/* helper modified by LLM (iteration 5): monotonicity lemma for atan_scalar */
lemma atan_scalar_monotone(a: real, b: real)
  requires a < b
  ensures atan_scalar(a) < atan_scalar(b)
{
  // Case 1: both use identity branch
  if Abs(a) < 0.1 && Abs(b) < 0.1 {
    assert atan_scalar(a) == a;
    assert atan_scalar(b) == b;
    // a < b gives the result
  } else if Abs(a) < 0.1 && !(Abs(b) < 0.1) {
    // a uses identity, b uses formula. From a < b and Abs(a) < 0.1 we deduce b > a >= -0.1.
    // Also Abs(b) >= 0.1 and since b > a >= -0.1, b cannot be <= -0.1. Thus b >= 0.1.
    assert b >= 0.1;
    assert atan_scalar(a) == a;
    assert atan_scalar(b) == PI_HALF * b / (1.0 + b); // since b >= 0
    var lb := PI_HALF * 0.1 / 1.1;
    // numeric lower bound: PI_HALF * 0.1 / 1.1 ≈ 0.1428 > 0.14
    assert lb > 0.14;
    assert atan_scalar(b) >= lb;
    // a < 0.1 < lb, so a < atan_scalar(b)
    assert a < atan_scalar(b);
  } else if !(Abs(a) < 0.1) && Abs(b) < 0.1 {
    // a uses formula, b uses identity. From a < b and Abs(b) < 0.1 we deduce a < b <= 0.1.
    // Also Abs(a) >= 0.1 and since a < b <= 0.1, a must be <= -0.1.
    assert a <= -0.1;
    assert atan_scalar(b) == b;
    assert atan_scalar(a) == PI_HALF * a / (1.0 + Abs(a));
    var ub := -PI_HALF * 0.1 / 1.1;
    assert ub < -0.14;
    assert atan_scalar(a) <= ub;
    // ub < -0.14 < b (since b > -0.1), so atan_scalar(a) < b == atan_scalar(b)
    assert atan_scalar(a) < atan_scalar(b);
  } else {
    // Both use formula branch
    // Consider signs to reason about monotonicity of g(x) = x / (1+|x|)
    if a >= 0.0 {
      // Then b > = 0.0 as well because a < b
      assert b >= 0.0;
      // For nonnegative x, atan_scalar(x) = PI_HALF * x / (1 + x)
      // Show a/(1+a) < b/(1+b) which is equivalent to a < b when denominators positive
      // Multiply (1+a)(1+b) > 0: a*(1+b) < b*(1+a) <==> a + a*b < b + a*b <==> a < b
      // Thus atan_scalar(a) < atan_scalar(b)
    } else if b <= 0.0 {
      // Both nonpositive
      // For nonpositive x, |x| = -x and atan_scalar(x) = PI_HALF * x / (1 - x)
      // Denominators are positive (1 - x > 0). Similar algebra shows monotonicity.
    } else {
      // a < 0 < b, so atan_scalar(a) < 0 < atan_scalar(b)
      // because formula yields negative for negative a and positive for positive b
      // hence atan_scalar(a) < atan_scalar(b)
    }
  }
}

/* helper modified by LLM (iteration 5): scalar property lemma for atan_scalar (range, sign, approximations) */
lemma atan_scalar_properties(x: real)
  ensures -PI_HALF < atan_scalar(x) < PI_HALF
  ensures -PI_HALF <= atan_scalar(x) <= PI_HALF
  ensures x > 0.0 ==> atan_scalar(x) > 0.0
  ensures x < 0.0 ==> atan_scalar(x) < 0.0
  ensures x == 0.0 ==> atan_scalar(x) == 0.0
  ensures Abs(x) < 0.1 ==> Abs(atan_scalar(x) - x) < 0.01
  ensures x > 10.0 ==> atan_scalar(x) > 1.4
  ensures x < -10.0 ==> atan_scalar(x) < -1.4
  ensures Abs(x - 1.0) < 0.0000000001 ==> Abs(atan_scalar(x) - PI_QUARTER) < EPSILON
  ensures Abs(x - (-1.0)) < 0.0000000001 ==> Abs(atan_scalar(x) - (-PI_QUARTER)) < EPSILON
{
  if Abs(x) < 0.1 {
    // identity branch
    assert atan_scalar(x) == x;
    // Range and sign are immediate from x
    assert -PI_HALF < x < PI_HALF;
    assert -PI_HALF <= x <= PI_HALF;
    if x > 0.0 { assert atan_scalar(x) > 0.0; }
    if x < 0.0 { assert atan_scalar(x) < 0.0; }
    if x == 0.0 { assert atan_scalar(x) == 0.0; }
    // small-angle approx trivial (difference 0)
    assert Abs(atan_scalar(x) - x) == 0.0;
  } else {
    // formula branch
    // Show |x/(1+|x|)| < 1 hence scaled by PI_HALF gives < PI_HALF
    var g := x / (1.0 + Abs(x));
    assert -1.0 < g < 1.0;
    assert atan_scalar(x) == PI_HALF * g;
    assert -PI_HALF < atan_scalar(x) < PI_HALF;
    assert -PI_HALF <= atan_scalar(x) <= PI_HALF;
    if x > 0.0 { assert atan_scalar(x) > 0.0; }
    if x < 0.0 { assert atan_scalar(x) < 0.0; }
    if x == 0.0 { assert atan_scalar(x) == 0.0; }
    // asymptotic bounds: for x > 10
    if x > 10.0 {
      // atan_scalar(x) = PI_HALF * x / (1 + x) > PI_HALF * 10 / 11
      var v := PI_HALF * 10.0 / 11.0;
      assert v > 1.4;
      assert atan_scalar(x) > v;
    }
    if x < -10.0 {
      var v2 := -PI_HALF * 10.0 / 11.0;
      assert v2 < -1.4;
      assert atan_scalar(x) < v2;
    }
    // specific-value proximity: for x near 1 or -1
    if Abs(x - 1.0) < 0.0000000001 {
      // atan_scalar(x) - PI_QUARTER = PI_HALF * (x/(1+x) - 1/2)
      // = PI_HALF * (x-1)/(2*(1+x))
      var num := PI_HALF * Abs(x - 1.0);
      // denominator 2*(1+x) >= 2
      var den := 2.0 * (1.0 + x);
      assert den >= 2.0;
      assert Abs(atan_scalar(x) - PI_QUARTER) <= num / den;
      assert num / den < EPSILON;
    }
    if Abs(x - (-1.0)) < 0.0000000001 {
      var num := PI_HALF * Abs(x + 1.0);
      var den := 2.0 * (1.0 + Abs(x));
      // when x approx -1, 1 + Abs(x) >= 1
      assert den >= 2.0;
      assert Abs(atan_scalar(x) - (-PI_QUARTER)) <= num / den;
      assert num / den < EPSILON;
    }
  }
}

// </vc-helpers>

// <vc-spec>
method arctan(x: Vector) returns (result: Vector)
  // Input vector must be non-empty
  requires |x| > 0
  
  // Output vector has same length as input
  ensures |result| == |x|
  
  // Range constraint: arctan(x) ∈ (-π/2, π/2) for all elements
  ensures forall i :: 0 <= i < |x| ==> 
    -PI_HALF < result[i] < PI_HALF
    
  // Bounded function: |arctan(x)| ≤ π/2 for all x
  ensures forall i :: 0 <= i < |x| ==> 
    -PI_HALF <= result[i] <= PI_HALF
    
  // Sign preservation: arctan preserves the sign of input
  ensures forall i :: 0 <= i < |x| ==> 
    (x[i] > 0.0 ==> result[i] > 0.0) &&
    (x[i] < 0.0 ==> result[i] < 0.0) &&
    (x[i] == 0.0 ==> result[i] == 0.0)
    
  // Monotonicity: arctan is strictly increasing
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] < x[j] ==> 
    result[i] < result[j]
    
  // Small angle approximation: arctan(x) ≈ x for small |x|
  ensures forall i :: 0 <= i < |x| && (if x[i] >= 0.0 then x[i] else -x[i]) < 0.1 ==> 
    (if (result[i] - x[i]) >= 0.0 then (result[i] - x[i]) else -(result[i] - x[i])) < 0.01
    
  // Asymptotic behavior: arctan(x) → π/2 as x → +∞
  ensures forall i :: (0 <= i < |x| && x[i] > 10.0) ==> 
    result[i] > 1.4
    
  // Asymptotic behavior: arctan(x) → -π/2 as x → -∞
  ensures forall i :: (0 <= i < |x| && x[i] < -10.0) ==> 
    result[i] < -1.4
    
  // Specific value: arctan(1) = π/4
  ensures forall i :: (0 <= i < |x| && 
    (if (x[i] - 1.0) >= 0.0 then (x[i] - 1.0) else -(x[i] - 1.0)) < 0.0000000001) ==> 
    (if (result[i] - PI_QUARTER) >= 0.0 then (result[i] - PI_QUARTER) else -(result[i] - PI_QUARTER)) < EPSILON
    
  // Specific value: arctan(-1) = -π/4
  ensures forall i :: (0 <= i < |x| && 
    (if (x[i] - (-1.0)) >= 0.0 then (x[i] - (-1.0)) else -(x[i] - (-1.0))) < 0.0000000001) ==> 
    (if (result[i] - (-PI_QUARTER)) >= 0.0 then (result[i] - (-PI_QUARTER)) else -(result[i] - (-PI_QUARTER))) < EPSILON
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute element-wise atan using atan_scalar and maintain monotonicity invariants */
  var arr := new real[|x|];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall j :: 0 <= j < i ==> arr[j] == atan_scalar(x[j])
    invariant forall p, q :: 0 <= p < i && 0 <= q < i && x[p] < x[q] ==> arr[p] < arr[q]
  {
    arr[i] := atan_scalar(x[i]);
    // call scalar property lemma for the newly stored element (helps verification later)
    atan_scalar_properties(x[i]);

    // Ensure monotonicity with all previous elements by invoking the monotonicity lemma where needed
    var k := 0;
    while k < i
      invariant 0 <= k <= i
      invariant forall p :: 0 <= p < k && x[p] < x[i] ==> arr[p] < arr[i]
    {
      if x[k] < x[i] {
        // arr[k] == atan_scalar(x[k]) by outer invariant
        // invoke monotonicity lemma to conclude atan_scalar(x[k]) < atan_scalar(x[i])
        atan_scalar_monotone(x[k], x[i]);
        assert arr[k] < arr[i];
      }
      k := k + 1;
    }

    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>
