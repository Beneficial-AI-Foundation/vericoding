// <vc-preamble>
/*
 * Calculate exp(x) - 1 for all elements in the vector.
 * This function provides greater precision than exp(x) - 1 for small values of x.
 * Implements element-wise expm1 computation with enhanced numerical precision.
 */

// Mathematical function declarations for specification
function Exp(x: real): real
{
  1.0 + x // Placeholder implementation for compilation
}

function Abs(x: real): real
  ensures Abs(x) >= 0.0
  ensures x >= 0.0 ==> Abs(x) == x
  ensures x < 0.0 ==> Abs(x) == -x
{
  if x >= 0.0 then x else -x
}

// Main expm1 method that computes exp(x) - 1 element-wise with enhanced precision
// </vc-preamble>

// <vc-helpers>
function Expm1Value(x: real): real
{
  Exp(x) - 1.0
}
// </vc-helpers>

// <vc-spec>
method Expm1(x: seq<real>) returns (result: seq<real>)
  // Output vector has same length as input
  ensures |result| == |x|
  // For each element i in the vectors, all mathematical properties hold
  ensures forall i :: 0 <= i < |x| ==> (
    // Basic mathematical property: result equals exp(x) - 1
    result[i] == Exp(x[i]) - 1.0 &&
    // Monotonicity property: expm1 is strictly increasing across elements
    (forall j :: 0 <= j < |x| && x[i] < x[j] ==> result[i] < result[j]) &&
    // Identity property: expm1(0) = 0
    (x[i] == 0.0 ==> result[i] == 0.0) &&
    // Asymptotic behavior for small values: exp(x) - 1 ≈ x for small x
    (Abs(x[i]) <= 0.1 ==> Abs(result[i] - x[i]) <= Abs(x[i]) * Abs(x[i])) &&
    // Sign preservation for small values
    (Abs(x[i]) <= 1.0 ==> ((x[i] > 0.0 ==> result[i] > 0.0) && (x[i] < 0.0 ==> result[i] < 0.0))) &&
    // Lower bound for positive values: expm1(x) > x for x > 0
    (x[i] > 0.0 ==> result[i] > x[i]) &&
    // Upper bound for all values: expm1(x) > -1 for all x
    result[i] > -1.0
  )
// </vc-spec>
// <vc-code>
{
  var res := [];
  var i := 0;
  
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> res[k] == Expm1Value(x[k])
    invariant forall k :: 0 <= k < i ==> res[k] == Exp(x[k]) - 1.0
    invariant forall k :: 0 <= k < i ==> (
      (forall j :: 0 <= j < |x| && x[k] < x[j] ==> res[k] < Exp(x[j]) - 1.0) &&
      (x[k] == 0.0 ==> res[k] == 0.0) &&
      (Abs(x[k]) <= 0.1 ==> Abs(res[k] - x[k]) <= Abs(x[k]) * Abs(x[k])) &&
      (Abs(x[k]) <= 1.0 ==> ((x[k] > 0.0 ==> res[k] > 0.0) && (x[k] < 0.0 ==> res[k] < 0.0))) &&
      (x[k] > 0.0 ==> res[k] > x[k]) &&
      res[k] > -1.0
    )
  {
    var val := Expm1Value(x[i]);
    res := res + [val];
    i := i + 1;
  }
  
  result := res;
}
// </vc-code>
