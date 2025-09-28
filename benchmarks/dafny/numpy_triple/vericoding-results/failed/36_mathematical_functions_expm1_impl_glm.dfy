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
// Helper function to compute expm1(x) with enhanced precision
function Expm1Single(x: real): real
  // Basic mathematical property: result equals exp(x) - 1
  ensures Expm1Single(x) == Exp(x) - 1.0
  // Identity property: expm1(0) = 0
  ensures x == 0.0 ==> Expm1Single(x) == 0.0
  // Asymptotic behavior for small values: exp(x) - 1 ≈ x for small x
  ensures Abs(x) <= 0.1 ==> Abs(Expm1Single(x) - x) <= Abs(x) * Abs(x)
  // Sign preservation for small values
  ensures Abs(x) <= 1.0 ==> ((x > 0.0 ==> Expm1Single(x) > 0.0) && (x < 0.0 ==> Expm1Single(x) < 0.0))
  // Lower bound for positive values: expm1(x) > x for x > 0
  ensures x > 0.0 ==> Expm1Single(x) > x
  // Upper bound for all values: expm1(x) > -1 for all x
  ensures Expm1Single(x) > -1.0
{
  if x == 0.0 then
    0.0
  else if Abs(x) <= 0.1 then
    // For small x, use a more accurate implementation than Exp(x) - 1.0
    // Using the Taylor series expansion: exp(x) - 1 = x + x²/2! + x³/3! + ...
    x + x * x / 2.0 + x * x * x / 6.0 + x * x * x * x / 24.0
  else
    // For larger x, use the direct computation
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
  var n := |x|;
  result := new real[n];
  
  for i := 0 to n
    invariant 0 <= i <= n
    invariant |result| == n
    invariant forall j :: 0 <= j < i ==> (
      result[j] == Exp(x[j]) - 1.0 &&
      (forall k :: 0 <= k < |x| && x[j] < x[k] ==> result[j] < result[k]) &&
      (x[j] == 0.0 ==> result[j] == 0.0) &&
      (Abs(x[j]) <= 0.1 ==> Abs(result[j] - x[j]) <= Abs(x[j]) * Abs(x[j])) &&
      (Abs(x[j]) <= 1.0 ==> ((x[j] > 0.0 ==> result[j] > 0.0) && (x[j] < 0.0 ==> result[j] < 0.0))) &&
      (x[j] > 0.0 ==> result[j] > x[j]) &&
      result[j] > -1.0
    )
  {
    result[i] := Expm1Single(x[i]);
  }
}
// </vc-code>
