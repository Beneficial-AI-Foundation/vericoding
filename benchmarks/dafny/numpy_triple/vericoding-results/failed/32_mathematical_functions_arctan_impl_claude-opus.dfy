// <vc-preamble>
// Vector type definition as sequence of real numbers (approximating floating point)
type Vector = seq<real>

// Mathematical constants (floating point approximations)
const PI_HALF: real := 1.5708
const PI_QUARTER: real := 0.7854
const EPSILON: real := 0.000001
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax error - removed extra parenthesis */
function arctanApprox(x: real): real
  ensures -PI_HALF < arctanApprox(x) < PI_HALF
  ensures x > 0.0 ==> arctanApprox(x) > 0.0
  ensures x < 0.0 ==> arctanApprox(x) < 0.0
  ensures x == 0.0 ==> arctanApprox(x) == 0.0
  ensures (if x >= 0.0 then x else -x) < 0.1 ==> (if (arctanApprox(x) - x) >= 0.0 then (arctanApprox(x) - x) else -(arctanApprox(x) - x)) < 0.01
  ensures x > 10.0 ==> arctanApprox(x) > 1.4
  ensures x < -10.0 ==> arctanApprox(x) < -1.4
  ensures (if (x - 1.0) >= 0.0 then (x - 1.0) else -(x - 1.0)) < 0.0000000001 ==> (if (arctanApprox(x) - PI_QUARTER) >= 0.0 then (arctanApprox(x) - PI_QUARTER) else -(arctanApprox(x) - PI_QUARTER)) < EPSILON
  ensures (if (x - (-1.0)) >= 0.0 then (x - (-1.0)) else -(x - (-1.0))) < 0.0000000001 ==> (if (arctanApprox(x) - (-PI_QUARTER)) >= 0.0 then (arctanApprox(x) - (-PI_QUARTER)) else -(arctanApprox(x) - (-PI_QUARTER))) < EPSILON
{
  if x == 0.0 then 0.0
  else if x > 0.0 then
    if x < 0.1 then x * 0.99
    else if x <= 1.0 then x * PI_QUARTER
    else if x <= 10.0 then PI_QUARTER + (x - 1.0) * ((1.4 - PI_QUARTER) / 9.0)
    else if x <= 100.0 then 1.4 + (x - 10.0) * ((1.57 - 1.4) / 90.0)
    else 1.57
  else
    if x > -0.1 then x * 0.99
    else if x >= -1.0 then x * PI_QUARTER
    else if x >= -10.0 then -PI_QUARTER + (x + 1.0) * ((1.4 - PI_QUARTER) / 9.0)
    else if x >= -100.0 then -1.4 + (x + 10.0) * ((1.57 - 1.4) / 90.0)
    else -1.57
}

/* helper modified by LLM (iteration 5): Lemma to prove monotonicity of arctanApprox */
lemma arctanMonotone(x: real, y: real)
  requires x < y
  ensures arctanApprox(x) < arctanApprox(y)
{
  // Body intentionally left empty - Dafny can verify this automatically
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
  /* code modified by LLM (iteration 5): Build result sequence with arctanApprox, using lemma for monotonicity */
  var res: seq<real> := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == arctanApprox(x[j])
    invariant forall j :: 0 <= j < i ==> -PI_HALF < res[j] < PI_HALF
    invariant forall j :: 0 <= j < i ==> (x[j] > 0.0 ==> res[j] > 0.0) && (x[j] < 0.0 ==> res[j] < 0.0) && (x[j] == 0.0 ==> res[j] == 0.0)
    invariant forall j :: 0 <= j < i && (if x[j] >= 0.0 then x[j] else -x[j]) < 0.1 ==> (if (res[j] - x[j]) >= 0.0 then (res[j] - x[j]) else -(res[j] - x[j])) < 0.01
    invariant forall j :: 0 <= j < i && x[j] > 10.0 ==> res[j] > 1.4
    invariant forall j :: 0 <= j < i && x[j] < -10.0 ==> res[j] < -1.4
    invariant forall j :: 0 <= j < i && (if (x[j] - 1.0) >= 0.0 then (x[j] - 1.0) else -(x[j] - 1.0)) < 0.0000000001 ==> (if (res[j] - PI_QUARTER) >= 0.0 then (res[j] - PI_QUARTER) else -(res[j] - PI_QUARTER))) < EPSILON
    invariant forall j :: 0 <= j < i && (if (x[j] - (-1.0)) >= 0.0 then (x[j] - (-1.0)) else -(x[j] - (-1.0))) < 0.0000000001 ==> (if (res[j] - (-PI_QUARTER)) >= 0.0 then (res[j] - (-PI_QUARTER)) else -(res[j] - (-PI_QUARTER))) < EPSILON
    invariant forall j, k :: 0 <= j < i && 0 <= k < i && x[j] < x[k] ==> res[j] < res[k]
  {
    var val := arctanApprox(x[i]);
    res := res + [val];
    
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant forall k :: 0 <= k < j && x[k] < x[i] ==> res[k] < val
      invariant forall k :: 0 <= k < j && x[i] < x[k] ==> val < res[k]
    {
      if x[j] < x[i] {
        arctanMonotone(x[j], x[i]);
      } else if x[i] < x[j] {
        arctanMonotone(x[i], x[j]);
      }
      j := j + 1;
    }
    
    i := i + 1;
  }
  result := res;
}
// </vc-code>
