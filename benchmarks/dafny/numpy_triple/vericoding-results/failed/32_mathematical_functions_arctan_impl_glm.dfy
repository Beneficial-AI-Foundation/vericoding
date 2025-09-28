// <vc-preamble>
// Vector type definition as sequence of real numbers (approximating floating point)
type Vector = seq<real>

// Mathematical constants (floating point approximations)
const PI_HALF: real := 1.5708
const PI_QUARTER: real := 0.7854
const EPSILON: real := 0.000001
// </vc-preamble>

// <vc-helpers>
const a1: real := -0.3333314528
const a2: real := 0.1999355085
const a3: real := -0.1420889944
const b1: real := -0.3333314528
const b2: real := -0.4667168330
const b3: real := 0.2434828980

/* helper modified by LLM (iteration 5): fixed let expressions by adding parentheses */
function arctan_single(x: real): real {
  if x == 1.0 then PI_QUARTER
  else if x == -1.0 then -PI_QUARTER
  else if Math.Abs(x) <= 1.0 then
    (let x2 := x*x in
     let x4 := x2*x2 in
     let x6 := x4*x2 in
     let num := x * (1.0 + a1*x2 + a2*x4 + a3*x6) in
     let den := 1.0 + b1*x2 + b2*x4 + b3*x6 in
     num / den)
  else
    (let z := 1.0 / Math.Abs(x) in
     let z2 := z*z in
     let z4 := z2*z2 in
     let z6 := z4*z2 in
     let num_small := z * (1.0 + a1*z2 + a2*z4 + a3*z6) in
     let den_small := 1.0 + b1*z2 + b2*z4 + b3*z6 in
     let inner := num_small / den_small in
     if x > 0.0 then
       PI_HALF - inner
     else
       -PI_HALF + inner)
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
  /* code modified by LLM (iteration 5): using fixed helper function */
  result := new real[|x|];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == |x|
    invariant forall j :: 0 <= j < i ==> result[j] == arctan_single(x[j])
  {
    result[i] := arctan_single(x[i]);
    i := i + 1;
  }
}
// </vc-code>
