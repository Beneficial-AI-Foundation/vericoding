// <vc-preamble>
// Vector type definition as sequence of real numbers (approximating floating point)
type Vector = seq<real>

// Mathematical constants (floating point approximations)
const PI_HALF: real := 1.5708
const PI_QUARTER: real := 0.7854
const EPSILON: real := 0.000001
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
